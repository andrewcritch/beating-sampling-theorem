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
import BstLean.Part269Direction30
import BstLean.Part269Shared30
import BstLean.Part269Finite
import BstLean.Part269Rows30
import BstLean.Part269Source
/-! Actual 13113 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13113 ≤ (1.035235875271 : ℝ) := by
  have hr : (114.512008103953 : ℝ) ≤ √(13113 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.512008103953 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13113 13113 (11 / 1000) ≤
    (0.008347481886 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13113) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.512008103953 : ℝ) ≤ √(13113 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13113)
  have hdiv : K / √(13113 : ℝ) ≤ K / 114.512008103953 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.512008103953 ≤ (0.008347481886 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13113.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13113 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13113 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13113 := gPlus_lower 13113
end BstLean.Part269.N13113

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13113
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035235875270 : ℝ) ≤ wn 13113 := by
  have hn : √(13113 : ℝ) ≤ 114.512008103954 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13113 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.512008103954 ≤ 2 / √(13113 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243812733 : ℝ) ≤ rhoBar 13113 BstLean.Part154.csC ∧
    rhoBar 13113 BstLean.Part154.csC ≤ 0.000243813111 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035235875270 : ℝ) / (1.295212 * 13113) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035235875271 : ℝ) / (1.29521 * 13113) := by gcongr
      _ ≤ (0.000243813111 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13113 BstLean.Part154.csC) ≤ 0.000975311889 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13113 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) ≤ 0.000186225821 ∧
    cc1 (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) ≤ 0.000118496784 ∧
    cc2 (rhoBar 13113 BstLean.Part154.csC) ≤ 0.000068788360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13113 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13113 BstLean.Part154.csC * nuR (rhoBar 13113 BstLean.Part154.csC)) ≤ 0.000487641084 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243813111 : ℝ) * 0.000975311889 := by gcongr
      _ ≤ (0.000487641084 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13113 BstLean.Part154.csC) * nuR (rhoBar 13113 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975311889 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13113 BstLean.Part154.csC) * rhoBar 13113 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243813111 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243813111 / 2 + 0.399 * 0.000975311889 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186225821 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487641084 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118496784 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243813111 / 1.414213562 := by gcongr
      _ ≤ (0.000068788360 : ℝ) := by norm_num

end BstLean.Part269.N13113

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13113
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) ≤ 1.49767E-7 := by
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13113 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13113 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186225821 : ℝ) ^ 2 + 0.000118496784 ^ 2 + 3 * 0.000068788360 ^ 2 +
        2 * 0.797885 * 0.000186225821 * 0.000118496784 + 2 * 0.000186225821 * 0.000068788360 +
        4 * 0.797885 * 0.000118496784 * 0.000068788360 := by gcongr
    _ ≤ (1.49767E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13113 BstLean.Part154.csC Θ ≤ 0.002543659955 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13113 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13113 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035235875271 * 1.49767E-7 / (0.000243812733 : ℝ) := by gcongr
    _ ≤ 0.002543659955 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13113 BstLean.Part154.csC Θ ≤ 0.002820760134 + 0.000642741844 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13113 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035235875271 : ℝ) * ((2 * Θ * 0.000243813111 +
        (6863 / 10000) * 0.000243813111 * 13113 * 0.000975311889) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002820760134 + 0.000642741844 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13113 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13113 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13113 0.011 Θ ∧ gammaRatio 13113 0.011 Θ ≤ 0.000083816643 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13113 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035235875271 : ℝ) * 0.525 / ((1 - 0.011) * 13113) := by gcongr
      _ ≤ (0.000083816643 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13113 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13113 0.011 Θ) :=
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
    badAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13113 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13113 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13113 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13113 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13113 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13113 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13113 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13113 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13113 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13113 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035235875271 : ℝ) * 13113 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003169665716 + 0.003186401799 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13113

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13113
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13113 BstLean.Part154.csC) (piBar (rhoBar 13113 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13113 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13113 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13113 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13113 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13113 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13113 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13113 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13113 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13113 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051642301058 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13113) ≤ 0.010428928816 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13113 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035235875271)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010428928816 + 2 * 0.737676 / 13113) := by gcongr
    _ ≤ (0.051642301058 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13113 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13113

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13113
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521657134 : ℝ) ≤ plow 13113 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13113) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349126661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335421477) : eMP 13113 0.011 xi bn ≤ 0.001150216718 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13113 : ℝ) * (1 - 0.011))) ≤ 0.000568767749 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335421477 / (13113 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568767749 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568767749 : ℝ) + 3.141593 * 0.052349126661 / (13113 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150216718 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349126661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335421477) : PiBarMP 13113 12 0.011 xi bn ≤ 0.158666295061 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13113 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036543419066 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.880450473292 : ℝ) ≤ √((13113 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.512008103953 : ℝ) ≤ √(13113 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13113) ≤ 0.121667661702 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036543419066 + 0.052349126661 * 1.772454 / (2 * (113.880450473292 : ℝ))) * (1 + 0.001150216718) +
        8 / (13113 * 114.512008103953) + 0.121667661702 := by gcongr
    _ ≤ (0.158666295061 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349126661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335421477) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280441616313) :
    parallelOracle 13113 0.011 xi bn cd ≤ 0.159625563818 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13113 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13113 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521657134 : ℝ) ≤ plow 13113 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.512008103953 : ℝ) ≤ √(13113 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280441616313 : ℝ) / (2 * 0.560521657134 * 114.512008103953)) * 0.158666295061 +
        0.280441616313 ^ 2 / (2 * 0.560521657134 * 114.512008103953) := by gcongr
    _ ≤ (0.159625563818 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052349126661) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335421477)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280441616313) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13113 13113 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521657134 : ℝ) ≤ plow 13113 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.512008103953 : ℝ) ≤ √(13113 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13113 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13113 Θ 1.22 ≤ 0.011580449265 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.512008103953 := by gcongr <;> linarith
      _ ≤ (0.011580449265 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13113 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13113 13113 0.011 ≤ 0.008347481886 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13113 13113 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13113 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13113 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13113 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13113 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159625563818 + 0.011580449265 + (0.008347481886 : ℝ) *
        (1 + 2 * (0.280441616313 + 0.011580449265) / (0.560521657134 * 114.512008103953))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13113]

end BstLean.Part269.N13113

/-! The original eight local profiles supply actual 13113 moment certificates. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13113 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052349126661 ∧
    0 ≤ bN 13113 BstLean.Part154.csC (groupTheta g) ∧ bN 13113 BstLean.Part154.csC (groupTheta g) ≤ 0.001335421477 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13113 13113 0.011
      (momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13113 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13113 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13113 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228799315255 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13113 0.011
      (momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13113 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13113
/-! The actual computed-centre upper energy formula at 13113. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13113

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13113)
open BstLean.Part268 (cell13113)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084369194058
  | 2 => 0.085294135548
  | 3 => 0.086214733598
  | 4 => 0.087131822152
  | 5 => 0.088046426600
  | 6 => 0.088959794240
  | 7 => 0.089873428016
  | 8 => 0.090789123612
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13113 13113 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13113 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13113

/-! Actual upper energy certificates on all 43 source endpoints at 13113. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13113)
open BstLean.Part268 (cell13113)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13113 (gMinus 13113) (1 - (cell13113 i).lower) ≤ 1 ∧
    energyUpper 13113 (gMinus 13113) (BstLean.Part211.gPlus 13113)
      (finiteEnergy 13113 13113 0.011) (1 - (cell13113 i).lower) ≤
      (cell13113 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨10,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨11,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨12,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨13,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨14,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨15,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨16,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨17,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨18,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨19,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨20,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨21,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨22,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨23,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨24,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨25,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨26,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨27,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨28,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨29,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨30,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨31,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨32,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨33,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨34,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨35,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨36,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨37,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨38,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨39,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨40,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨41,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨42,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨43,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨44,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨45,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨46,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨47,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨48,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨49,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨50,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨51,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13113) (by norm_num)
        (q := 1 - (cell13113 ⟨52,by decide⟩).lower)
        (by norm_num [cell13113]) (by norm_num [cell13113])
      exact ⟨E.1,E.2.trans (by norm_num [cell13113])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13113

/-! Source-cell containment and simple scalar guards at 13113. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13113)
open BstLean.Part268 (cell13113)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13113 ⟨10,by decide⟩).lower ∧ (cell13113 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13113 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13113 ⟨11,by decide⟩).lower ∧ (cell13113 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13113 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13113 ⟨12,by decide⟩).lower ∧ (cell13113 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13113 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13113 ⟨13,by decide⟩).lower ∧ (cell13113 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13113 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13113 ⟨14,by decide⟩).lower ∧ (cell13113 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13113 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13113 ⟨15,by decide⟩).lower ∧ (cell13113 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13113 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13113 ⟨16,by decide⟩).lower ∧ (cell13113 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13113 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13113 ⟨17,by decide⟩).lower ∧ (cell13113 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13113 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13113 ⟨18,by decide⟩).lower ∧ (cell13113 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13113 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13113 ⟨19,by decide⟩).lower ∧ (cell13113 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13113 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13113 ⟨20,by decide⟩).lower ∧ (cell13113 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13113 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13113 ⟨21,by decide⟩).lower ∧ (cell13113 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13113 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13113 ⟨22,by decide⟩).lower ∧ (cell13113 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13113 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13113 ⟨23,by decide⟩).lower ∧ (cell13113 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13113 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13113 ⟨24,by decide⟩).lower ∧ (cell13113 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13113 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13113 ⟨25,by decide⟩).lower ∧ (cell13113 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13113 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13113 ⟨26,by decide⟩).lower ∧ (cell13113 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13113 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13113 ⟨27,by decide⟩).lower ∧ (cell13113 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13113 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13113 ⟨28,by decide⟩).lower ∧ (cell13113 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13113 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13113 ⟨29,by decide⟩).lower ∧ (cell13113 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13113 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13113 ⟨30,by decide⟩).lower ∧ (cell13113 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13113 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13113 ⟨31,by decide⟩).lower ∧ (cell13113 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13113 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13113 ⟨32,by decide⟩).lower ∧ (cell13113 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13113 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13113 ⟨33,by decide⟩).lower ∧ (cell13113 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13113 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13113 ⟨34,by decide⟩).lower ∧ (cell13113 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13113 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13113 ⟨35,by decide⟩).lower ∧ (cell13113 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13113 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13113 ⟨36,by decide⟩).lower ∧ (cell13113 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13113 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13113 ⟨37,by decide⟩).lower ∧ (cell13113 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13113 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13113 ⟨38,by decide⟩).lower ∧ (cell13113 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13113 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13113 ⟨39,by decide⟩).lower ∧ (cell13113 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13113 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13113 ⟨40,by decide⟩).lower ∧ (cell13113 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13113 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13113 ⟨41,by decide⟩).lower ∧ (cell13113 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13113 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13113 ⟨42,by decide⟩).lower ∧ (cell13113 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13113 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13113 ⟨43,by decide⟩).lower ∧ (cell13113 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13113 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13113 ⟨44,by decide⟩).lower ∧ (cell13113 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13113 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13113 ⟨45,by decide⟩).lower ∧ (cell13113 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13113 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13113 ⟨46,by decide⟩).lower ∧ (cell13113 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13113 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13113 ⟨47,by decide⟩).lower ∧ (cell13113 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13113 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13113 ⟨48,by decide⟩).lower ∧ (cell13113 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13113 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13113 ⟨49,by decide⟩).lower ∧ (cell13113 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13113 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13113 ⟨50,by decide⟩).lower ∧ (cell13113 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13113 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13113 ⟨51,by decide⟩).lower ∧ (cell13113 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13113 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13113 ⟨52,by decide⟩).lower ∧ (cell13113 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13113 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13113 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13113 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13113,cell13113,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13113 i).lower ∧
    (cell13113 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13113 i).upper ≤ (0.532 : ℝ) ∧
    (cell13113 i).centre ≤ (0.1 : ℝ) ∧ (cell13113 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13113 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13113 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13113

/-! The local source numeric instances at 13113 have no network premises. -/
namespace BstLean.Part269.N13113
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13113)
open BstLean.Part268 (cell13113)

noncomputable def sourceNumerics13113 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13113 (cell13113 i)
      scalarRow13113.M scalarRow13113.H scalarRow13113.xi := by
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
    energy_allowance := scalarRow13113.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13113]
    centre_nonneg := (scalarRow13113.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13113])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13113
/-! Actual 13114 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13114 ≤ (1.035234520170 : ℝ) := by
  have hr : (114.516374375021 : ℝ) ≤ √(13114 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.516374375021 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13114 13114 (11 / 1000) ≤
    (0.008347163612 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13114) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.516374375021 : ℝ) ≤ √(13114 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13114)
  have hdiv : K / √(13114 : ℝ) ≤ K / 114.516374375021 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.516374375021 ≤ (0.008347163612 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13114.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13114 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13114 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13114 := gPlus_lower 13114
end BstLean.Part269.N13114

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13114
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035234520169 : ℝ) ≤ wn 13114 := by
  have hn : √(13114 : ℝ) ≤ 114.516374375022 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13114 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.516374375022 ≤ 2 / √(13114 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243793823 : ℝ) ≤ rhoBar 13114 BstLean.Part154.csC ∧
    rhoBar 13114 BstLean.Part154.csC ≤ 0.000243794200 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035234520169 : ℝ) / (1.295212 * 13114) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035234520170 : ℝ) / (1.29521 * 13114) := by gcongr
      _ ≤ (0.000243794200 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13114 BstLean.Part154.csC) ≤ 0.000975236236 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13114 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) ≤ 0.000186211377 ∧
    cc1 (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) ≤ 0.000118487592 ∧
    cc2 (rhoBar 13114 BstLean.Part154.csC) ≤ 0.000068783025 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13114 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13114 BstLean.Part154.csC * nuR (rhoBar 13114 BstLean.Part154.csC)) ≤ 0.000487603259 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243794200 : ℝ) * 0.000975236236 := by gcongr
      _ ≤ (0.000487603259 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13114 BstLean.Part154.csC) * nuR (rhoBar 13114 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975236236 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13114 BstLean.Part154.csC) * rhoBar 13114 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243794200 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243794200 / 2 + 0.399 * 0.000975236236 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186211377 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487603259 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118487592 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243794200 / 1.414213562 := by gcongr
      _ ≤ (0.000068783025 : ℝ) := by norm_num

end BstLean.Part269.N13114

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13114
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) ≤ 1.49744E-7 := by
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13114 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13114 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186211377 : ℝ) ^ 2 + 0.000118487592 ^ 2 + 3 * 0.000068783025 ^ 2 +
        2 * 0.797885 * 0.000186211377 * 0.000118487592 + 2 * 0.000186211377 * 0.000068783025 +
        4 * 0.797885 * 0.000118487592 * 0.000068783025 := by gcongr
    _ ≤ (1.49744E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13114 BstLean.Part154.csC Θ ≤ 0.002543463261 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13114 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13114 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035234520170 * 1.49744E-7 / (0.000243793823 : ℝ) := by gcongr
    _ ≤ 0.002543463261 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13114 BstLean.Part154.csC Θ ≤ 0.002820533949 + 0.000642691150 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13114 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035234520170 : ℝ) * ((2 * Θ * 0.000243794200 +
        (6863 / 10000) * 0.000243794200 * 13114 * 0.000975236236) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002820533949 + 0.000642691150 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13114 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13114 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13114 0.011 Θ ∧ gammaRatio 13114 0.011 Θ ≤ 0.000083810142 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13114 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035234520170 : ℝ) * 0.525 / ((1 - 0.011) * 13114) := by gcongr
      _ ≤ (0.000083810142 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13114 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13114 0.011 Θ) :=
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
    badAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13114 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13114 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13114 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13114 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13114 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13114 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13114 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13114 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13114 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13114 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035234520170 : ℝ) * 13114 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003169439531 + 0.003186154411 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13114

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13114
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13114 BstLean.Part154.csC) (piBar (rhoBar 13114 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13114 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13114 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13114 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13114 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13114 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13114 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13114 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13114 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13114 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051640311032 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13114) ≤ 0.010428531183 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13114 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035234520170)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010428531183 + 2 * 0.737676 / 13114) := by gcongr
    _ ≤ (0.051640311032 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13114 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13114

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13114
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521699550 : ℝ) ≤ plow 13114 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13114) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348770597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335318213) : eMP 13114 0.011 xi bn ≤ 0.001150128312 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13114 : ℝ) * (1 - 0.011))) ≤ 0.000568724073 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335318213 / (13114 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568724073 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568724073 : ℝ) + 3.141593 * 0.052348770597 / (13114 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150128312 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348770597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335318213) : PiBarMP 13114 12 0.011 xi bn ≤ 0.158660219378 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13114 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036542006144 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.884792663463 : ℝ) ≤ √((13114 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.516374375021 : ℝ) ≤ √(13114 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13114) ≤ 0.121663022767 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036542006144 + 0.052348770597 * 1.772454 / (2 * (113.884792663463 : ℝ))) * (1 + 0.001150128312) +
        8 / (13114 * 114.516374375021) + 0.121663022767 := by gcongr
    _ ≤ (0.158660219378 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348770597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335318213) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280438848172) :
    parallelOracle 13114 0.011 xi bn cd ≤ 0.159619422700 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13114 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13114 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521699550 : ℝ) ≤ plow 13114 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.516374375021 : ℝ) ≤ √(13114 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280438848172 : ℝ) / (2 * 0.560521699550 * 114.516374375021)) * 0.158660219378 +
        0.280438848172 ^ 2 / (2 * 0.560521699550 * 114.516374375021) := by gcongr
    _ ≤ (0.159619422700 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348770597) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335318213)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280438848172) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13114 13114 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521699550 : ℝ) ≤ plow 13114 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.516374375021 : ℝ) ≤ √(13114 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13114 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13114 Θ 1.22 ≤ 0.011580007726 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.516374375021 := by gcongr <;> linarith
      _ ≤ (0.011580007726 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13114 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13114 13114 0.011 ≤ 0.008347163612 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13114 13114 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13114 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13114 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13114 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13114 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159619422700 + 0.011580007726 + (0.008347163612 : ℝ) *
        (1 + 2 * (0.280438848172 + 0.011580007726) / (0.560521699550 * 114.516374375021))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13114]

end BstLean.Part269.N13114

/-! The original eight local profiles supply actual 13114 moment certificates. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13114 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052348770597 ∧
    0 ≤ bN 13114 BstLean.Part154.csC (groupTheta g) ∧ bN 13114 BstLean.Part154.csC (groupTheta g) ≤ 0.001335318213 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13114 13114 0.011
      (momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13114 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13114 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13114 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228798537140 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13114 0.011
      (momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13114 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13114
/-! The actual computed-centre upper energy formula at 13114. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13114

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13114)
open BstLean.Part268 (cell13114)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084366662517
  | 2 => 0.085291572459
  | 3 => 0.086212134427
  | 4 => 0.087129181287
  | 5 => 0.088043737149
  | 6 => 0.088957047805
  | 7 => 0.089870614434
  | 8 => 0.090786230672
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13114 13114 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13114 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13114

/-! Actual upper energy certificates on all 43 source endpoints at 13114. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13114)
open BstLean.Part268 (cell13114)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13114 (gMinus 13114) (1 - (cell13114 i).lower) ≤ 1 ∧
    energyUpper 13114 (gMinus 13114) (BstLean.Part211.gPlus 13114)
      (finiteEnergy 13114 13114 0.011) (1 - (cell13114 i).lower) ≤
      (cell13114 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨10,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨11,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨12,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨13,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨14,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨15,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨16,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨17,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨18,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨19,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨20,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨21,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨22,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨23,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨24,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨25,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨26,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨27,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨28,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨29,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨30,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨31,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨32,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨33,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨34,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨35,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨36,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨37,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨38,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨39,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨40,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨41,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨42,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨43,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨44,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨45,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨46,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨47,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨48,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨49,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨50,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨51,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13114) (by norm_num)
        (q := 1 - (cell13114 ⟨52,by decide⟩).lower)
        (by norm_num [cell13114]) (by norm_num [cell13114])
      exact ⟨E.1,E.2.trans (by norm_num [cell13114])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13114

/-! Source-cell containment and simple scalar guards at 13114. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13114)
open BstLean.Part268 (cell13114)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13114 ⟨10,by decide⟩).lower ∧ (cell13114 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13114 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13114 ⟨11,by decide⟩).lower ∧ (cell13114 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13114 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13114 ⟨12,by decide⟩).lower ∧ (cell13114 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13114 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13114 ⟨13,by decide⟩).lower ∧ (cell13114 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13114 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13114 ⟨14,by decide⟩).lower ∧ (cell13114 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13114 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13114 ⟨15,by decide⟩).lower ∧ (cell13114 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13114 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13114 ⟨16,by decide⟩).lower ∧ (cell13114 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13114 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13114 ⟨17,by decide⟩).lower ∧ (cell13114 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13114 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13114 ⟨18,by decide⟩).lower ∧ (cell13114 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13114 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13114 ⟨19,by decide⟩).lower ∧ (cell13114 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13114 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13114 ⟨20,by decide⟩).lower ∧ (cell13114 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13114 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13114 ⟨21,by decide⟩).lower ∧ (cell13114 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13114 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13114 ⟨22,by decide⟩).lower ∧ (cell13114 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13114 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13114 ⟨23,by decide⟩).lower ∧ (cell13114 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13114 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13114 ⟨24,by decide⟩).lower ∧ (cell13114 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13114 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13114 ⟨25,by decide⟩).lower ∧ (cell13114 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13114 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13114 ⟨26,by decide⟩).lower ∧ (cell13114 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13114 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13114 ⟨27,by decide⟩).lower ∧ (cell13114 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13114 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13114 ⟨28,by decide⟩).lower ∧ (cell13114 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13114 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13114 ⟨29,by decide⟩).lower ∧ (cell13114 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13114 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13114 ⟨30,by decide⟩).lower ∧ (cell13114 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13114 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13114 ⟨31,by decide⟩).lower ∧ (cell13114 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13114 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13114 ⟨32,by decide⟩).lower ∧ (cell13114 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13114 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13114 ⟨33,by decide⟩).lower ∧ (cell13114 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13114 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13114 ⟨34,by decide⟩).lower ∧ (cell13114 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13114 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13114 ⟨35,by decide⟩).lower ∧ (cell13114 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13114 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13114 ⟨36,by decide⟩).lower ∧ (cell13114 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13114 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13114 ⟨37,by decide⟩).lower ∧ (cell13114 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13114 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13114 ⟨38,by decide⟩).lower ∧ (cell13114 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13114 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13114 ⟨39,by decide⟩).lower ∧ (cell13114 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13114 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13114 ⟨40,by decide⟩).lower ∧ (cell13114 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13114 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13114 ⟨41,by decide⟩).lower ∧ (cell13114 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13114 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13114 ⟨42,by decide⟩).lower ∧ (cell13114 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13114 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13114 ⟨43,by decide⟩).lower ∧ (cell13114 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13114 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13114 ⟨44,by decide⟩).lower ∧ (cell13114 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13114 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13114 ⟨45,by decide⟩).lower ∧ (cell13114 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13114 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13114 ⟨46,by decide⟩).lower ∧ (cell13114 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13114 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13114 ⟨47,by decide⟩).lower ∧ (cell13114 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13114 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13114 ⟨48,by decide⟩).lower ∧ (cell13114 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13114 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13114 ⟨49,by decide⟩).lower ∧ (cell13114 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13114 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13114 ⟨50,by decide⟩).lower ∧ (cell13114 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13114 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13114 ⟨51,by decide⟩).lower ∧ (cell13114 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13114 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13114 ⟨52,by decide⟩).lower ∧ (cell13114 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13114 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13114 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13114 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13114,cell13114,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13114 i).lower ∧
    (cell13114 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13114 i).upper ≤ (0.532 : ℝ) ∧
    (cell13114 i).centre ≤ (0.1 : ℝ) ∧ (cell13114 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13114 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13114 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13114

/-! The local source numeric instances at 13114 have no network premises. -/
namespace BstLean.Part269.N13114
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13114)
open BstLean.Part268 (cell13114)

noncomputable def sourceNumerics13114 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13114 (cell13114 i)
      scalarRow13114.M scalarRow13114.H scalarRow13114.xi := by
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
    energy_allowance := scalarRow13114.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13114]
    centre_nonneg := (scalarRow13114.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13114])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13114
/-! Actual 13115 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13115 ≤ (1.035233165225 : ℝ) := by
  have hr : (114.520740479617 : ℝ) ≤ √(13115 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.520740479617 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13115 13115 (11 / 1000) ≤
    (0.008346845373 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13115) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.520740479617 : ℝ) ≤ √(13115 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13115)
  have hdiv : K / √(13115 : ℝ) ≤ K / 114.520740479617 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.520740479617 ≤ (0.008346845373 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13115.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13115 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13115 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13115 := gPlus_lower 13115
end BstLean.Part269.N13115

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13115
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035233165224 : ℝ) ≤ wn 13115 := by
  have hn : √(13115 : ℝ) ≤ 114.520740479618 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13115 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.520740479618 ≤ 2 / √(13115 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243774915 : ℝ) ≤ rhoBar 13115 BstLean.Part154.csC ∧
    rhoBar 13115 BstLean.Part154.csC ≤ 0.000243775292 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035233165224 : ℝ) / (1.295212 * 13115) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035233165225 : ℝ) / (1.29521 * 13115) := by gcongr
      _ ≤ (0.000243775292 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13115 BstLean.Part154.csC) ≤ 0.000975160595 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13115 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) ≤ 0.000186196934 ∧
    cc1 (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) ≤ 0.000118478403 ∧
    cc2 (rhoBar 13115 BstLean.Part154.csC) ≤ 0.000068777690 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13115 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13115 BstLean.Part154.csC * nuR (rhoBar 13115 BstLean.Part154.csC)) ≤ 0.000487565441 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243775292 : ℝ) * 0.000975160595 := by gcongr
      _ ≤ (0.000487565441 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13115 BstLean.Part154.csC) * nuR (rhoBar 13115 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975160595 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13115 BstLean.Part154.csC) * rhoBar 13115 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243775292 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243775292 / 2 + 0.399 * 0.000975160595 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186196934 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487565441 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118478403 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243775292 / 1.414213562 := by gcongr
      _ ≤ (0.000068777690 : ℝ) := by norm_num

end BstLean.Part269.N13115

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13115
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) ≤ 1.49720E-7 := by
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13115 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13115 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186196934 : ℝ) ^ 2 + 0.000118478403 ^ 2 + 3 * 0.000068777690 ^ 2 +
        2 * 0.797885 * 0.000186196934 * 0.000118478403 + 2 * 0.000186196934 * 0.000068777690 +
        4 * 0.797885 * 0.000118478403 * 0.000068777690 := by gcongr
    _ ≤ (1.49720E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13115 BstLean.Part154.csC Θ ≤ 0.002543249530 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13115 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13115 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035233165225 * 1.49720E-7 / (0.000243774915 : ℝ) := by gcongr
    _ ≤ 0.002543249530 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13115 BstLean.Part154.csC Θ ≤ 0.002820307801 + 0.000642640463 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13115 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035233165225 : ℝ) * ((2 * Θ * 0.000243775292 +
        (6863 / 10000) * 0.000243775292 * 13115 * 0.000975160595) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002820307801 + 0.000642640463 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13115 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13115 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13115 0.011 Θ ∧ gammaRatio 13115 0.011 Θ ≤ 0.000083803642 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13115 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035233165225 : ℝ) * 0.525 / ((1 - 0.011) * 13115) := by gcongr
      _ ≤ (0.000083803642 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13115 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13115 0.011 Θ) :=
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
    badAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13115 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13115 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13115 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13115 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13115 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13115 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13115 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13115 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13115 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13115 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035233165225 : ℝ) * 13115 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003169213383 + 0.003185889993 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13115

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13115
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13115 BstLean.Part154.csC) (piBar (rhoBar 13115 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13115 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13115 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13115 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13115 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13115 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13115 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13115 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13115 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13115 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051638321232 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13115) ≤ 0.010428133595 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13115 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035233165225)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010428133595 + 2 * 0.737676 / 13115) := by gcongr
    _ ≤ (0.051638321232 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13115 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13115

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13115
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521741959 : ℝ) ≤ plow 13115 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13115) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348405630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335206004) : eMP 13115 0.011 xi bn ≤ 0.001150036101 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13115 : ℝ) * (1 - 0.011))) ≤ 0.000568678495 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335206004 / (13115 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568678495 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568678495 : ℝ) + 3.141593 * 0.052348405630 / (13115 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001150036101 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348405630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335206004) : PiBarMP 13115 12 0.011 xi bn ≤ 0.158654021425 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13115 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036540470769 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.889134688081 : ℝ) ≤ √((13115 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.520740479617 : ℝ) ≤ √(13115 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13115) ≤ 0.121658384363 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036540470769 + 0.052348405630 * 1.772454 / (2 * (113.889134688081 : ℝ))) * (1 + 0.001150036101) +
        8 / (13115 * 114.520740479617) + 0.121658384363 := by gcongr
    _ ≤ (0.158654021425 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348405630)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335206004) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280436060797) :
    parallelOracle 13115 0.011 xi bn cd ≤ 0.159613158944 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13115 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13115 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521741959 : ℝ) ≤ plow 13115 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.520740479617 : ℝ) ≤ √(13115 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280436060797 : ℝ) / (2 * 0.560521741959 * 114.520740479617)) * 0.158654021425 +
        0.280436060797 ^ 2 / (2 * 0.560521741959 * 114.520740479617) := by gcongr
    _ ≤ (0.159613158944 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348405630) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335206004)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280436060797) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13115 13115 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521741959 : ℝ) ≤ plow 13115 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.520740479617 : ℝ) ≤ √(13115 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13115 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13115 Θ 1.22 ≤ 0.011579566238 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.520740479617 := by gcongr <;> linarith
      _ ≤ (0.011579566238 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13115 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13115 13115 0.011 ≤ 0.008346845373 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13115 13115 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13115 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13115 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13115 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13115 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159613158944 + 0.011579566238 + (0.008346845373 : ℝ) *
        (1 + 2 * (0.280436060797 + 0.011579566238) / (0.560521741959 * 114.520740479617))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13115]

end BstLean.Part269.N13115

/-! The original eight local profiles supply actual 13115 moment certificates. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13115 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052348405630 ∧
    0 ≤ bN 13115 BstLean.Part154.csC (groupTheta g) ∧ bN 13115 BstLean.Part154.csC (groupTheta g) ≤ 0.001335206004 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13115 13115 0.011
      (momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13115 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13115 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13115 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228797739565 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13115 0.011
      (momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13115 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13115
/-! The actual computed-centre upper energy formula at 13115. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13115

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13115)
open BstLean.Part268 (cell13115)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084364131705
  | 2 => 0.085289010122
  | 3 => 0.086209536039
  | 4 => 0.087126541244
  | 5 => 0.088041048566
  | 6 => 0.088954302294
  | 7 => 0.089867801845
  | 8 => 0.090783338809
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13115 13115 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13115 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13115

/-! Actual upper energy certificates on all 43 source endpoints at 13115. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13115)
open BstLean.Part268 (cell13115)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13115 (gMinus 13115) (1 - (cell13115 i).lower) ≤ 1 ∧
    energyUpper 13115 (gMinus 13115) (BstLean.Part211.gPlus 13115)
      (finiteEnergy 13115 13115 0.011) (1 - (cell13115 i).lower) ≤
      (cell13115 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨10,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨11,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨12,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨13,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨14,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨15,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨16,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨17,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨18,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨19,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨20,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨21,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨22,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨23,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨24,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨25,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨26,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨27,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨28,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨29,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨30,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨31,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨32,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨33,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨34,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨35,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨36,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨37,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨38,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨39,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨40,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨41,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨42,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨43,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨44,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨45,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨46,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨47,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨48,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨49,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨50,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨51,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13115) (by norm_num)
        (q := 1 - (cell13115 ⟨52,by decide⟩).lower)
        (by norm_num [cell13115]) (by norm_num [cell13115])
      exact ⟨E.1,E.2.trans (by norm_num [cell13115])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13115

/-! Source-cell containment and simple scalar guards at 13115. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13115)
open BstLean.Part268 (cell13115)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13115 ⟨10,by decide⟩).lower ∧ (cell13115 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13115 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13115 ⟨11,by decide⟩).lower ∧ (cell13115 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13115 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13115 ⟨12,by decide⟩).lower ∧ (cell13115 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13115 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13115 ⟨13,by decide⟩).lower ∧ (cell13115 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13115 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13115 ⟨14,by decide⟩).lower ∧ (cell13115 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13115 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13115 ⟨15,by decide⟩).lower ∧ (cell13115 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13115 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13115 ⟨16,by decide⟩).lower ∧ (cell13115 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13115 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13115 ⟨17,by decide⟩).lower ∧ (cell13115 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13115 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13115 ⟨18,by decide⟩).lower ∧ (cell13115 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13115 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13115 ⟨19,by decide⟩).lower ∧ (cell13115 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13115 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13115 ⟨20,by decide⟩).lower ∧ (cell13115 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13115 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13115 ⟨21,by decide⟩).lower ∧ (cell13115 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13115 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13115 ⟨22,by decide⟩).lower ∧ (cell13115 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13115 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13115 ⟨23,by decide⟩).lower ∧ (cell13115 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13115 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13115 ⟨24,by decide⟩).lower ∧ (cell13115 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13115 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13115 ⟨25,by decide⟩).lower ∧ (cell13115 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13115 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13115 ⟨26,by decide⟩).lower ∧ (cell13115 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13115 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13115 ⟨27,by decide⟩).lower ∧ (cell13115 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13115 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13115 ⟨28,by decide⟩).lower ∧ (cell13115 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13115 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13115 ⟨29,by decide⟩).lower ∧ (cell13115 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13115 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13115 ⟨30,by decide⟩).lower ∧ (cell13115 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13115 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13115 ⟨31,by decide⟩).lower ∧ (cell13115 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13115 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13115 ⟨32,by decide⟩).lower ∧ (cell13115 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13115 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13115 ⟨33,by decide⟩).lower ∧ (cell13115 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13115 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13115 ⟨34,by decide⟩).lower ∧ (cell13115 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13115 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13115 ⟨35,by decide⟩).lower ∧ (cell13115 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13115 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13115 ⟨36,by decide⟩).lower ∧ (cell13115 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13115 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13115 ⟨37,by decide⟩).lower ∧ (cell13115 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13115 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13115 ⟨38,by decide⟩).lower ∧ (cell13115 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13115 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13115 ⟨39,by decide⟩).lower ∧ (cell13115 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13115 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13115 ⟨40,by decide⟩).lower ∧ (cell13115 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13115 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13115 ⟨41,by decide⟩).lower ∧ (cell13115 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13115 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13115 ⟨42,by decide⟩).lower ∧ (cell13115 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13115 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13115 ⟨43,by decide⟩).lower ∧ (cell13115 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13115 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13115 ⟨44,by decide⟩).lower ∧ (cell13115 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13115 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13115 ⟨45,by decide⟩).lower ∧ (cell13115 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13115 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13115 ⟨46,by decide⟩).lower ∧ (cell13115 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13115 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13115 ⟨47,by decide⟩).lower ∧ (cell13115 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13115 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13115 ⟨48,by decide⟩).lower ∧ (cell13115 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13115 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13115 ⟨49,by decide⟩).lower ∧ (cell13115 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13115 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13115 ⟨50,by decide⟩).lower ∧ (cell13115 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13115 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13115 ⟨51,by decide⟩).lower ∧ (cell13115 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13115 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13115 ⟨52,by decide⟩).lower ∧ (cell13115 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13115 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13115 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13115 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13115,cell13115,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13115 i).lower ∧
    (cell13115 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13115 i).upper ≤ (0.532 : ℝ) ∧
    (cell13115 i).centre ≤ (0.1 : ℝ) ∧ (cell13115 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13115 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13115 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13115

/-! The local source numeric instances at 13115 have no network premises. -/
namespace BstLean.Part269.N13115
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13115)
open BstLean.Part268 (cell13115)

noncomputable def sourceNumerics13115 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13115 (cell13115 i)
      scalarRow13115.M scalarRow13115.H scalarRow13115.xi := by
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
    energy_allowance := scalarRow13115.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13115]
    centre_nonneg := (scalarRow13115.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13115])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13115
/-! Actual 13116 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13116 ≤ (1.035231810436 : ℝ) := by
  have hr : (114.525106417763 : ℝ) ≤ √(13116 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.525106417763 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13116 13116 (11 / 1000) ≤
    (0.008346527172 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13116) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.525106417763 : ℝ) ≤ √(13116 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13116)
  have hdiv : K / √(13116 : ℝ) ≤ K / 114.525106417763 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.525106417763 ≤ (0.008346527172 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13116.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13116 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13116 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13116 := gPlus_lower 13116
end BstLean.Part269.N13116

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13116
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035231810435 : ℝ) ≤ wn 13116 := by
  have hn : √(13116 : ℝ) ≤ 114.525106417764 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13116 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.525106417764 ≤ 2 / √(13116 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243756009 : ℝ) ≤ rhoBar 13116 BstLean.Part154.csC ∧
    rhoBar 13116 BstLean.Part154.csC ≤ 0.000243756387 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035231810435 : ℝ) / (1.295212 * 13116) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035231810436 : ℝ) / (1.29521 * 13116) := by gcongr
      _ ≤ (0.000243756387 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13116 BstLean.Part154.csC) ≤ 0.000975084966 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13116 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) ≤ 0.000186182493 ∧
    cc1 (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) ≤ 0.000118469214 ∧
    cc2 (rhoBar 13116 BstLean.Part154.csC) ≤ 0.000068772356 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13116 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13116 BstLean.Part154.csC * nuR (rhoBar 13116 BstLean.Part154.csC)) ≤ 0.000487527629 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243756387 : ℝ) * 0.000975084966 := by gcongr
      _ ≤ (0.000487527629 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13116 BstLean.Part154.csC) * nuR (rhoBar 13116 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975084966 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13116 BstLean.Part154.csC) * rhoBar 13116 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243756387 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243756387 / 2 + 0.399 * 0.000975084966 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186182493 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487527629 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118469214 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243756387 / 1.414213562 := by gcongr
      _ ≤ (0.000068772356 : ℝ) := by norm_num

end BstLean.Part269.N13116

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13116
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) ≤ 1.49697E-7 := by
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13116 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13116 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186182493 : ℝ) ^ 2 + 0.000118469214 ^ 2 + 3 * 0.000068772356 ^ 2 +
        2 * 0.797885 * 0.000186182493 * 0.000118469214 + 2 * 0.000186182493 * 0.000068772356 +
        4 * 0.797885 * 0.000118469214 * 0.000068772356 := by gcongr
    _ ≤ (1.49697E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13116 BstLean.Part154.csC Θ ≤ 0.002543052735 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13116 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13116 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035231810436 * 1.49697E-7 / (0.000243756009 : ℝ) := by gcongr
    _ ≤ 0.002543052735 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13116 BstLean.Part154.csC Θ ≤ 0.002820081691 + 0.000642589785 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13116 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035231810436 : ℝ) * ((2 * Θ * 0.000243756387 +
        (6863 / 10000) * 0.000243756387 * 13116 * 0.000975084966) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002820081691 + 0.000642589785 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13116 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13116 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13116 0.011 Θ ∧ gammaRatio 13116 0.011 Θ ≤ 0.000083797143 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13116 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035231810436 : ℝ) * 0.525 / ((1 - 0.011) * 13116) := by gcongr
      _ ≤ (0.000083797143 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13116 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13116 0.011 Θ) :=
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
    badAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13116 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13116 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13116 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13116 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13116 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13116 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13116 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13116 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13116 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13116 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035231810436 : ℝ) * 13116 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003168987273 + 0.003185642520 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13116

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13116
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13116 BstLean.Part154.csC) (piBar (rhoBar 13116 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13116 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13116 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13116 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13116 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13116 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13116 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13116 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13116 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13116 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051636331664 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13116) ≤ 0.010427736053 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13116 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035231810436)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010427736053 + 2 * 0.737676 / 13116) := by gcongr
    _ ≤ (0.051636331664 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13116 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13116

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13116
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521784362 : ℝ) ≤ plow 13116 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13116) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348049596)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335102686) : eMP 13116 0.011 xi bn ≤ 0.001149947686 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13116 : ℝ) * (1 - 0.011))) ≤ 0.000568634814 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001335102686 / (13116 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568634814 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568634814 : ℝ) + 3.141593 * 0.052348049596 / (13116 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149947686 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348049596)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335102686) : PiBarMP 13116 12 0.011 xi bn ≤ 0.158647945954 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13116 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036539056994 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.893476547166 : ℝ) ≤ √((13116 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.525106417763 : ℝ) ≤ √(13116 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13116) ≤ 0.121653746489 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036539056994 + 0.052348049596 * 1.772454 / (2 * (113.893476547166 : ℝ))) * (1 + 0.001149947686) +
        8 / (13116 * 114.525106417763) + 0.121653746489 := by gcongr
    _ ≤ (0.158647945954 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348049596)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335102686) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280433293174) :
    parallelOracle 13116 0.011 xi bn cd ≤ 0.159607018055 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13116 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13116 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521784362 : ℝ) ≤ plow 13116 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.525106417763 : ℝ) ≤ √(13116 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280433293174 : ℝ) / (2 * 0.560521784362 * 114.525106417763)) * 0.158647945954 +
        0.280433293174 ^ 2 / (2 * 0.560521784362 * 114.525106417763) := by gcongr
    _ ≤ (0.159607018055 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052348049596) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001335102686)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280433293174) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13116 13116 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521784362 : ℝ) ≤ plow 13116 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.525106417763 : ℝ) ≤ √(13116 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13116 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13116 Θ 1.22 ≤ 0.011579124801 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.525106417763 := by gcongr <;> linarith
      _ ≤ (0.011579124801 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13116 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13116 13116 0.011 ≤ 0.008346527172 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13116 13116 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13116 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13116 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13116 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13116 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159607018055 + 0.011579124801 + (0.008346527172 : ℝ) *
        (1 + 2 * (0.280433293174 + 0.011579124801) / (0.560521784362 * 114.525106417763))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13116]

end BstLean.Part269.N13116

/-! The original eight local profiles supply actual 13116 moment certificates. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13116 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052348049596 ∧
    0 ≤ bN 13116 BstLean.Part154.csC (groupTheta g) ∧ bN 13116 BstLean.Part154.csC (groupTheta g) ≤ 0.001335102686 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13116 13116 0.011
      (momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13116 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13116 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13116 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228796961510 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13116 0.011
      (momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13116 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13116
/-! The actual computed-centre upper energy formula at 13116. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13116

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13116)
open BstLean.Part268 (cell13116)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084361601621
  | 2 => 0.085286448538
  | 3 => 0.086206938434
  | 4 => 0.087123902021
  | 5 => 0.088038360850
  | 6 => 0.088951557706
  | 7 => 0.089864990250
  | 8 => 0.090780448022
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13116 13116 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13116 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13116

/-! Actual upper energy certificates on all 43 source endpoints at 13116. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13116)
open BstLean.Part268 (cell13116)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13116 (gMinus 13116) (1 - (cell13116 i).lower) ≤ 1 ∧
    energyUpper 13116 (gMinus 13116) (BstLean.Part211.gPlus 13116)
      (finiteEnergy 13116 13116 0.011) (1 - (cell13116 i).lower) ≤
      (cell13116 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨10,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨11,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨12,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨13,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨14,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨15,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨16,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨17,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨18,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨19,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨20,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨21,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨22,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨23,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨24,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨25,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨26,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨27,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨28,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨29,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨30,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨31,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨32,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨33,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨34,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨35,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨36,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨37,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨38,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨39,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨40,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨41,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨42,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨43,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨44,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨45,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨46,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨47,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨48,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨49,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨50,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨51,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13116) (by norm_num)
        (q := 1 - (cell13116 ⟨52,by decide⟩).lower)
        (by norm_num [cell13116]) (by norm_num [cell13116])
      exact ⟨E.1,E.2.trans (by norm_num [cell13116])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13116

/-! Source-cell containment and simple scalar guards at 13116. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13116)
open BstLean.Part268 (cell13116)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13116 ⟨10,by decide⟩).lower ∧ (cell13116 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13116 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13116 ⟨11,by decide⟩).lower ∧ (cell13116 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13116 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13116 ⟨12,by decide⟩).lower ∧ (cell13116 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13116 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13116 ⟨13,by decide⟩).lower ∧ (cell13116 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13116 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13116 ⟨14,by decide⟩).lower ∧ (cell13116 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13116 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13116 ⟨15,by decide⟩).lower ∧ (cell13116 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13116 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13116 ⟨16,by decide⟩).lower ∧ (cell13116 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13116 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13116 ⟨17,by decide⟩).lower ∧ (cell13116 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13116 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13116 ⟨18,by decide⟩).lower ∧ (cell13116 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13116 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13116 ⟨19,by decide⟩).lower ∧ (cell13116 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13116 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13116 ⟨20,by decide⟩).lower ∧ (cell13116 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13116 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13116 ⟨21,by decide⟩).lower ∧ (cell13116 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13116 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13116 ⟨22,by decide⟩).lower ∧ (cell13116 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13116 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13116 ⟨23,by decide⟩).lower ∧ (cell13116 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13116 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13116 ⟨24,by decide⟩).lower ∧ (cell13116 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13116 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13116 ⟨25,by decide⟩).lower ∧ (cell13116 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13116 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13116 ⟨26,by decide⟩).lower ∧ (cell13116 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13116 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13116 ⟨27,by decide⟩).lower ∧ (cell13116 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13116 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13116 ⟨28,by decide⟩).lower ∧ (cell13116 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13116 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13116 ⟨29,by decide⟩).lower ∧ (cell13116 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13116 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13116 ⟨30,by decide⟩).lower ∧ (cell13116 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13116 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13116 ⟨31,by decide⟩).lower ∧ (cell13116 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13116 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13116 ⟨32,by decide⟩).lower ∧ (cell13116 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13116 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13116 ⟨33,by decide⟩).lower ∧ (cell13116 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13116 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13116 ⟨34,by decide⟩).lower ∧ (cell13116 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13116 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13116 ⟨35,by decide⟩).lower ∧ (cell13116 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13116 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13116 ⟨36,by decide⟩).lower ∧ (cell13116 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13116 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13116 ⟨37,by decide⟩).lower ∧ (cell13116 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13116 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13116 ⟨38,by decide⟩).lower ∧ (cell13116 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13116 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13116 ⟨39,by decide⟩).lower ∧ (cell13116 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13116 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13116 ⟨40,by decide⟩).lower ∧ (cell13116 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13116 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13116 ⟨41,by decide⟩).lower ∧ (cell13116 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13116 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13116 ⟨42,by decide⟩).lower ∧ (cell13116 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13116 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13116 ⟨43,by decide⟩).lower ∧ (cell13116 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13116 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13116 ⟨44,by decide⟩).lower ∧ (cell13116 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13116 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13116 ⟨45,by decide⟩).lower ∧ (cell13116 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13116 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13116 ⟨46,by decide⟩).lower ∧ (cell13116 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13116 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13116 ⟨47,by decide⟩).lower ∧ (cell13116 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13116 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13116 ⟨48,by decide⟩).lower ∧ (cell13116 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13116 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13116 ⟨49,by decide⟩).lower ∧ (cell13116 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13116 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13116 ⟨50,by decide⟩).lower ∧ (cell13116 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13116 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13116 ⟨51,by decide⟩).lower ∧ (cell13116 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13116 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13116 ⟨52,by decide⟩).lower ∧ (cell13116 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13116 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13116 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13116 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13116,cell13116,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13116 i).lower ∧
    (cell13116 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13116 i).upper ≤ (0.532 : ℝ) ∧
    (cell13116 i).centre ≤ (0.1 : ℝ) ∧ (cell13116 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13116 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13116 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13116

/-! The local source numeric instances at 13116 have no network premises. -/
namespace BstLean.Part269.N13116
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13116)
open BstLean.Part268 (cell13116)

noncomputable def sourceNumerics13116 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13116 (cell13116 i)
      scalarRow13116.M scalarRow13116.H scalarRow13116.xi := by
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
    energy_allowance := scalarRow13116.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13116]
    centre_nonneg := (scalarRow13116.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13116])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13116
/-! Actual 13117 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13117 ≤ (1.035230455803 : ℝ) := by
  have hr : (114.529472189476 : ℝ) ≤ √(13117 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.529472189476 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13117 13117 (11 / 1000) ≤
    (0.008346209006 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13117) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.529472189476 : ℝ) ≤ √(13117 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13117)
  have hdiv : K / √(13117 : ℝ) ≤ K / 114.529472189476 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.529472189476 ≤ (0.008346209006 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13117.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13117 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13117 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13117 := gPlus_lower 13117
end BstLean.Part269.N13117

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13117
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035230455802 : ℝ) ≤ wn 13117 := by
  have hn : √(13117 : ℝ) ≤ 114.529472189477 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13117 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.529472189477 ≤ 2 / √(13117 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243737107 : ℝ) ≤ rhoBar 13117 BstLean.Part154.csC ∧
    rhoBar 13117 BstLean.Part154.csC ≤ 0.000243737485 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035230455802 : ℝ) / (1.295212 * 13117) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035230455803 : ℝ) / (1.29521 * 13117) := by gcongr
      _ ≤ (0.000243737485 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13117 BstLean.Part154.csC) ≤ 0.000975009348 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13117 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) ≤ 0.000186168055 ∧
    cc1 (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) ≤ 0.000118460027 ∧
    cc2 (rhoBar 13117 BstLean.Part154.csC) ≤ 0.000068767023 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13117 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13117 BstLean.Part154.csC * nuR (rhoBar 13117 BstLean.Part154.csC)) ≤ 0.000487489822 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243737485 : ℝ) * 0.000975009348 := by gcongr
      _ ≤ (0.000487489822 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13117 BstLean.Part154.csC) * nuR (rhoBar 13117 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000975009348 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13117 BstLean.Part154.csC) * rhoBar 13117 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243737485 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243737485 / 2 + 0.399 * 0.000975009348 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186168055 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487489822 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118460027 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243737485 / 1.414213562 := by gcongr
      _ ≤ (0.000068767023 : ℝ) := by norm_num

end BstLean.Part269.N13117

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13117
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) ≤ 1.49674E-7 := by
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13117 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13117 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186168055 : ℝ) ^ 2 + 0.000118460027 ^ 2 + 3 * 0.000068767023 ^ 2 +
        2 * 0.797885 * 0.000186168055 * 0.000118460027 + 2 * 0.000186168055 * 0.000068767023 +
        4 * 0.797885 * 0.000118460027 * 0.000068767023 := by gcongr
    _ ≤ (1.49674E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13117 BstLean.Part154.csC Θ ≤ 0.002542855869 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13117 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13117 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035230455803 * 1.49674E-7 / (0.000243737107 : ℝ) := by gcongr
    _ ≤ 0.002542855869 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13117 BstLean.Part154.csC Θ ≤ 0.002819855615 + 0.000642539115 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13117 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035230455803 : ℝ) * ((2 * Θ * 0.000243737485 +
        (6863 / 10000) * 0.000243737485 * 13117 * 0.000975009348) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002819855615 + 0.000642539115 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13117 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13117 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13117 0.011 Θ ∧ gammaRatio 13117 0.011 Θ ≤ 0.000083790645 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13117 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035230455803 : ℝ) * 0.525 / ((1 - 0.011) * 13117) := by gcongr
      _ ≤ (0.000083790645 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13117 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13117 0.011 Θ) :=
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
    badAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13117 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13117 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13117 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13117 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13117 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13117 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13117 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13117 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13117 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13117 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035230455803 : ℝ) * 13117 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003168761197 + 0.003185394984 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13117

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13117
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13117 BstLean.Part154.csC) (piBar (rhoBar 13117 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13117 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13117 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13117 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13117 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13117 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13117 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13117 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13117 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13117 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051634342323 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13117) ≤ 0.010427338556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13117 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035230455803)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010427338556 + 2 * 0.737676 / 13117) := by gcongr
    _ ≤ (0.051634342323 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13117 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13117

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13117
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521826759 : ℝ) ≤ plow 13117 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13117) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347693564)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334999332) : eMP 13117 0.011 xi bn ≤ 0.001149859264 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13117 : ℝ) * (1 - 0.011))) ≤ 0.000568591129 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334999332 / (13117 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568591129 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568591129 : ℝ) + 3.141593 * 0.052347693564 / (13117 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149859264 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347693564)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334999332) : PiBarMP 13117 12 0.011 xi bn ≤ 0.158641870468 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13117 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036537642672 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.897818240737 : ℝ) ≤ √((13117 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.529472189476 : ℝ) ≤ √(13117 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13117) ≤ 0.121649109146 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036537642672 + 0.052347693564 * 1.772454 / (2 * (113.897818240737 : ℝ))) * (1 + 0.001149859264) +
        8 / (13117 * 114.529472189476) + 0.121649109146 := by gcongr
    _ ≤ (0.158641870468 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347693564)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334999332) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280430525779) :
    parallelOracle 13117 0.011 xi bn cd ≤ 0.159600877159 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13117 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13117 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521826759 : ℝ) ≤ plow 13117 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.529472189476 : ℝ) ≤ √(13117 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280430525779 : ℝ) / (2 * 0.560521826759 * 114.529472189476)) * 0.158641870468 +
        0.280430525779 ^ 2 / (2 * 0.560521826759 * 114.529472189476) := by gcongr
    _ ≤ (0.159600877159 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347693564) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334999332)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280430525779) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13117 13117 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521826759 : ℝ) ≤ plow 13117 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.529472189476 : ℝ) ≤ √(13117 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13117 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13117 Θ 1.22 ≤ 0.011578683414 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.529472189476 := by gcongr <;> linarith
      _ ≤ (0.011578683414 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13117 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13117 13117 0.011 ≤ 0.008346209006 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13117 13117 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13117 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13117 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13117 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13117 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159600877159 + 0.011578683414 + (0.008346209006 : ℝ) *
        (1 + 2 * (0.280430525779 + 0.011578683414) / (0.560521826759 * 114.529472189476))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13117]

end BstLean.Part269.N13117

/-! The original eight local profiles supply actual 13117 moment certificates. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13117 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052347693564 ∧
    0 ≤ bN 13117 BstLean.Part154.csC (groupTheta g) ∧ bN 13117 BstLean.Part154.csC (groupTheta g) ≤ 0.001334999332 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13117 13117 0.011
      (momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13117 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13117 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13117 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228796183456 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13117 0.011
      (momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13117 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13117
/-! The actual computed-centre upper energy formula at 13117. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13117

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13117)
open BstLean.Part268 (cell13117)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084359072263
  | 2 => 0.085283887706
  | 3 => 0.086204341612
  | 4 => 0.087121263617
  | 5 => 0.088035674000
  | 6 => 0.088948814042
  | 7 => 0.089862179646
  | 8 => 0.090777558311
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13117 13117 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13117 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13117

/-! Actual upper energy certificates on all 43 source endpoints at 13117. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13117)
open BstLean.Part268 (cell13117)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13117 (gMinus 13117) (1 - (cell13117 i).lower) ≤ 1 ∧
    energyUpper 13117 (gMinus 13117) (BstLean.Part211.gPlus 13117)
      (finiteEnergy 13117 13117 0.011) (1 - (cell13117 i).lower) ≤
      (cell13117 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨10,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨11,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨12,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨13,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨14,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨15,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨16,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨17,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨18,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨19,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨20,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨21,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨22,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨23,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨24,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨25,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨26,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨27,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨28,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨29,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨30,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨31,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨32,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨33,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨34,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨35,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨36,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨37,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨38,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨39,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨40,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨41,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨42,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨43,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨44,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨45,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨46,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨47,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨48,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨49,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨50,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨51,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13117) (by norm_num)
        (q := 1 - (cell13117 ⟨52,by decide⟩).lower)
        (by norm_num [cell13117]) (by norm_num [cell13117])
      exact ⟨E.1,E.2.trans (by norm_num [cell13117])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13117

/-! Source-cell containment and simple scalar guards at 13117. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13117)
open BstLean.Part268 (cell13117)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13117 ⟨10,by decide⟩).lower ∧ (cell13117 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13117 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13117 ⟨11,by decide⟩).lower ∧ (cell13117 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13117 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13117 ⟨12,by decide⟩).lower ∧ (cell13117 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13117 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13117 ⟨13,by decide⟩).lower ∧ (cell13117 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13117 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13117 ⟨14,by decide⟩).lower ∧ (cell13117 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13117 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13117 ⟨15,by decide⟩).lower ∧ (cell13117 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13117 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13117 ⟨16,by decide⟩).lower ∧ (cell13117 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13117 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13117 ⟨17,by decide⟩).lower ∧ (cell13117 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13117 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13117 ⟨18,by decide⟩).lower ∧ (cell13117 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13117 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13117 ⟨19,by decide⟩).lower ∧ (cell13117 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13117 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13117 ⟨20,by decide⟩).lower ∧ (cell13117 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13117 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13117 ⟨21,by decide⟩).lower ∧ (cell13117 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13117 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13117 ⟨22,by decide⟩).lower ∧ (cell13117 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13117 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13117 ⟨23,by decide⟩).lower ∧ (cell13117 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13117 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13117 ⟨24,by decide⟩).lower ∧ (cell13117 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13117 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13117 ⟨25,by decide⟩).lower ∧ (cell13117 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13117 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13117 ⟨26,by decide⟩).lower ∧ (cell13117 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13117 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13117 ⟨27,by decide⟩).lower ∧ (cell13117 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13117 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13117 ⟨28,by decide⟩).lower ∧ (cell13117 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13117 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13117 ⟨29,by decide⟩).lower ∧ (cell13117 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13117 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13117 ⟨30,by decide⟩).lower ∧ (cell13117 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13117 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13117 ⟨31,by decide⟩).lower ∧ (cell13117 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13117 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13117 ⟨32,by decide⟩).lower ∧ (cell13117 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13117 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13117 ⟨33,by decide⟩).lower ∧ (cell13117 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13117 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13117 ⟨34,by decide⟩).lower ∧ (cell13117 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13117 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13117 ⟨35,by decide⟩).lower ∧ (cell13117 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13117 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13117 ⟨36,by decide⟩).lower ∧ (cell13117 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13117 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13117 ⟨37,by decide⟩).lower ∧ (cell13117 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13117 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13117 ⟨38,by decide⟩).lower ∧ (cell13117 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13117 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13117 ⟨39,by decide⟩).lower ∧ (cell13117 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13117 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13117 ⟨40,by decide⟩).lower ∧ (cell13117 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13117 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13117 ⟨41,by decide⟩).lower ∧ (cell13117 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13117 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13117 ⟨42,by decide⟩).lower ∧ (cell13117 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13117 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13117 ⟨43,by decide⟩).lower ∧ (cell13117 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13117 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13117 ⟨44,by decide⟩).lower ∧ (cell13117 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13117 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13117 ⟨45,by decide⟩).lower ∧ (cell13117 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13117 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13117 ⟨46,by decide⟩).lower ∧ (cell13117 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13117 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13117 ⟨47,by decide⟩).lower ∧ (cell13117 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13117 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13117 ⟨48,by decide⟩).lower ∧ (cell13117 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13117 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13117 ⟨49,by decide⟩).lower ∧ (cell13117 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13117 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13117 ⟨50,by decide⟩).lower ∧ (cell13117 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13117 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13117 ⟨51,by decide⟩).lower ∧ (cell13117 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13117 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13117 ⟨52,by decide⟩).lower ∧ (cell13117 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13117 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13117 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13117 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13117,cell13117,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13117 i).lower ∧
    (cell13117 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13117 i).upper ≤ (0.532 : ℝ) ∧
    (cell13117 i).centre ≤ (0.1 : ℝ) ∧ (cell13117 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13117 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13117 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13117

/-! The local source numeric instances at 13117 have no network premises. -/
namespace BstLean.Part269.N13117
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13117)
open BstLean.Part268 (cell13117)

noncomputable def sourceNumerics13117 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13117 (cell13117 i)
      scalarRow13117.M scalarRow13117.H scalarRow13117.xi := by
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
    energy_allowance := scalarRow13117.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13117]
    centre_nonneg := (scalarRow13117.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13117])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13117
/-! Actual 13118 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13118 ≤ (1.035229101325 : ℝ) := by
  have hr : (114.533837794775 : ℝ) ≤ √(13118 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.533837794775 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13118 13118 (11 / 1000) ≤
    (0.008345890878 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13118) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.533837794775 : ℝ) ≤ √(13118 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13118)
  have hdiv : K / √(13118 : ℝ) ≤ K / 114.533837794775 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.533837794775 ≤ (0.008345890878 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13118.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13118 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13118 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13118 := gPlus_lower 13118
end BstLean.Part269.N13118

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13118
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035229101324 : ℝ) ≤ wn 13118 := by
  have hn : √(13118 : ℝ) ≤ 114.533837794776 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13118 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.533837794776 ≤ 2 / √(13118 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243718208 : ℝ) ≤ rhoBar 13118 BstLean.Part154.csC ∧
    rhoBar 13118 BstLean.Part154.csC ≤ 0.000243718585 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035229101324 : ℝ) / (1.295212 * 13118) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035229101325 : ℝ) / (1.29521 * 13118) := by gcongr
      _ ≤ (0.000243718585 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13118 BstLean.Part154.csC) ≤ 0.000974933739 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13118 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) ≤ 0.000186153619 ∧
    cc1 (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) ≤ 0.000118450841 ∧
    cc2 (rhoBar 13118 BstLean.Part154.csC) ≤ 0.000068761691 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13118 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13118 BstLean.Part154.csC * nuR (rhoBar 13118 BstLean.Part154.csC)) ≤ 0.000487452020 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243718585 : ℝ) * 0.000974933739 := by gcongr
      _ ≤ (0.000487452020 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13118 BstLean.Part154.csC) * nuR (rhoBar 13118 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974933739 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13118 BstLean.Part154.csC) * rhoBar 13118 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243718585 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243718585 / 2 + 0.399 * 0.000974933739 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186153619 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487452020 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118450841 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243718585 / 1.414213562 := by gcongr
      _ ≤ (0.000068761691 : ℝ) := by norm_num

end BstLean.Part269.N13118

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13118
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) ≤ 1.49651E-7 := by
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13118 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13118 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186153619 : ℝ) ^ 2 + 0.000118450841 ^ 2 + 3 * 0.000068761691 ^ 2 +
        2 * 0.797885 * 0.000186153619 * 0.000118450841 + 2 * 0.000186153619 * 0.000068761691 +
        4 * 0.797885 * 0.000118450841 * 0.000068761691 := by gcongr
    _ ≤ (1.49651E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13118 BstLean.Part154.csC Θ ≤ 0.002542658943 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13118 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13118 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035229101325 * 1.49651E-7 / (0.000243718208 : ℝ) := by gcongr
    _ ≤ 0.002542658943 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13118 BstLean.Part154.csC Θ ≤ 0.002819629557 + 0.000642488450 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13118 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035229101325 : ℝ) * ((2 * Θ * 0.000243718585 +
        (6863 / 10000) * 0.000243718585 * 13118 * 0.000974933739) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002819629557 + 0.000642488450 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13118 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13118 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13118 0.011 Θ ∧ gammaRatio 13118 0.011 Θ ≤ 0.000083784148 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13118 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035229101325 : ℝ) * 0.525 / ((1 - 0.011) * 13118) := by gcongr
      _ ≤ (0.000083784148 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13118 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13118 0.011 Θ) :=
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
    badAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13118 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13118 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13118 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13118 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13118 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13118 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13118 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13118 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13118 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13118 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035229101325 : ℝ) * 13118 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003168535139 + 0.003185147393 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13118

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13118
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13118 BstLean.Part154.csC) (piBar (rhoBar 13118 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13118 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13118 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13118 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13118 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13118 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13118 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13118 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13118 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13118 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051632353209 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13118) ≤ 0.010426941104 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13118 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035229101325)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010426941104 + 2 * 0.737676 / 13118) := by gcongr
    _ ≤ (0.051632353209 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13118 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13118

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13118
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521869149 : ℝ) ≤ plow 13118 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13118) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347337521)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334895946) : eMP 13118 0.011 xi bn ≤ 0.001149770833 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13118 : ℝ) * (1 - 0.011))) ≤ 0.000568547440 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334895946 / (13118 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568547440 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568547440 : ℝ) + 3.141593 * 0.052347337521 / (13118 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149770833 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347337521)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334895946) : PiBarMP 13118 12 0.011 xi bn ≤ 0.158635795021 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13118 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036536227857 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.902159768812 : ℝ) ≤ √((13118 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.533837794775 : ℝ) ≤ √(13118 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13118) ≤ 0.121644472333 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036536227857 + 0.052347337521 * 1.772454 / (2 * (113.902159768812 : ℝ))) * (1 + 0.001149770833) +
        8 / (13118 * 114.533837794775) + 0.121644472333 := by gcongr
    _ ≤ (0.158635795021 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347337521)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334895946) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280427758585) :
    parallelOracle 13118 0.011 xi bn cd ≤ 0.159594736310 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13118 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13118 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521869149 : ℝ) ≤ plow 13118 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.533837794775 : ℝ) ≤ √(13118 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280427758585 : ℝ) / (2 * 0.560521869149 * 114.533837794775)) * 0.158635795021 +
        0.280427758585 ^ 2 / (2 * 0.560521869149 * 114.533837794775) := by gcongr
    _ ≤ (0.159594736310 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052347337521) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334895946)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280427758585) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13118 13118 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521869149 : ℝ) ≤ plow 13118 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.533837794775 : ℝ) ≤ √(13118 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13118 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13118 Θ 1.22 ≤ 0.011578242078 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.533837794775 := by gcongr <;> linarith
      _ ≤ (0.011578242078 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13118 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13118 13118 0.011 ≤ 0.008345890878 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13118 13118 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13118 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13118 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13118 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13118 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159594736310 + 0.011578242078 + (0.008345890878 : ℝ) *
        (1 + 2 * (0.280427758585 + 0.011578242078) / (0.560521869149 * 114.533837794775))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13118]

end BstLean.Part269.N13118

/-! The original eight local profiles supply actual 13118 moment certificates. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13118 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052347337521 ∧
    0 ≤ bN 13118 BstLean.Part154.csC (groupTheta g) ∧ bN 13118 BstLean.Part154.csC (groupTheta g) ≤ 0.001334895946 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13118 13118 0.011
      (momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13118 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13118 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13118 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228795405376 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13118 0.011
      (momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13118 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13118
/-! The actual computed-centre upper energy formula at 13118. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13118

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13118)
open BstLean.Part268 (cell13118)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084356543632
  | 2 => 0.085281327624
  | 3 => 0.086201745571
  | 4 => 0.087118626033
  | 5 => 0.088032988015
  | 6 => 0.088946071299
  | 7 => 0.089859370033
  | 8 => 0.090774669673
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13118 13118 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13118 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13118

/-! Actual upper energy certificates on all 43 source endpoints at 13118. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13118)
open BstLean.Part268 (cell13118)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13118 (gMinus 13118) (1 - (cell13118 i).lower) ≤ 1 ∧
    energyUpper 13118 (gMinus 13118) (BstLean.Part211.gPlus 13118)
      (finiteEnergy 13118 13118 0.011) (1 - (cell13118 i).lower) ≤
      (cell13118 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨10,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨11,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨12,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨13,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨14,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨15,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨16,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨17,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨18,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨19,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨20,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨21,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨22,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨23,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨24,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨25,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨26,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨27,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨28,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨29,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨30,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨31,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨32,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨33,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨34,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨35,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨36,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨37,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨38,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨39,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨40,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨41,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨42,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨43,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨44,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨45,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨46,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨47,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨48,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨49,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨50,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨51,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13118) (by norm_num)
        (q := 1 - (cell13118 ⟨52,by decide⟩).lower)
        (by norm_num [cell13118]) (by norm_num [cell13118])
      exact ⟨E.1,E.2.trans (by norm_num [cell13118])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13118

/-! Source-cell containment and simple scalar guards at 13118. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13118)
open BstLean.Part268 (cell13118)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13118 ⟨10,by decide⟩).lower ∧ (cell13118 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13118 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13118 ⟨11,by decide⟩).lower ∧ (cell13118 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13118 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13118 ⟨12,by decide⟩).lower ∧ (cell13118 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13118 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13118 ⟨13,by decide⟩).lower ∧ (cell13118 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13118 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13118 ⟨14,by decide⟩).lower ∧ (cell13118 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13118 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13118 ⟨15,by decide⟩).lower ∧ (cell13118 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13118 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13118 ⟨16,by decide⟩).lower ∧ (cell13118 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13118 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13118 ⟨17,by decide⟩).lower ∧ (cell13118 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13118 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13118 ⟨18,by decide⟩).lower ∧ (cell13118 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13118 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13118 ⟨19,by decide⟩).lower ∧ (cell13118 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13118 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13118 ⟨20,by decide⟩).lower ∧ (cell13118 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13118 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13118 ⟨21,by decide⟩).lower ∧ (cell13118 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13118 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13118 ⟨22,by decide⟩).lower ∧ (cell13118 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13118 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13118 ⟨23,by decide⟩).lower ∧ (cell13118 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13118 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13118 ⟨24,by decide⟩).lower ∧ (cell13118 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13118 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13118 ⟨25,by decide⟩).lower ∧ (cell13118 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13118 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13118 ⟨26,by decide⟩).lower ∧ (cell13118 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13118 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13118 ⟨27,by decide⟩).lower ∧ (cell13118 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13118 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13118 ⟨28,by decide⟩).lower ∧ (cell13118 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13118 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13118 ⟨29,by decide⟩).lower ∧ (cell13118 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13118 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13118 ⟨30,by decide⟩).lower ∧ (cell13118 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13118 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13118 ⟨31,by decide⟩).lower ∧ (cell13118 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13118 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13118 ⟨32,by decide⟩).lower ∧ (cell13118 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13118 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13118 ⟨33,by decide⟩).lower ∧ (cell13118 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13118 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13118 ⟨34,by decide⟩).lower ∧ (cell13118 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13118 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13118 ⟨35,by decide⟩).lower ∧ (cell13118 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13118 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13118 ⟨36,by decide⟩).lower ∧ (cell13118 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13118 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13118 ⟨37,by decide⟩).lower ∧ (cell13118 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13118 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13118 ⟨38,by decide⟩).lower ∧ (cell13118 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13118 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13118 ⟨39,by decide⟩).lower ∧ (cell13118 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13118 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13118 ⟨40,by decide⟩).lower ∧ (cell13118 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13118 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13118 ⟨41,by decide⟩).lower ∧ (cell13118 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13118 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13118 ⟨42,by decide⟩).lower ∧ (cell13118 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13118 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13118 ⟨43,by decide⟩).lower ∧ (cell13118 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13118 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13118 ⟨44,by decide⟩).lower ∧ (cell13118 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13118 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13118 ⟨45,by decide⟩).lower ∧ (cell13118 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13118 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13118 ⟨46,by decide⟩).lower ∧ (cell13118 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13118 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13118 ⟨47,by decide⟩).lower ∧ (cell13118 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13118 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13118 ⟨48,by decide⟩).lower ∧ (cell13118 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13118 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13118 ⟨49,by decide⟩).lower ∧ (cell13118 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13118 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13118 ⟨50,by decide⟩).lower ∧ (cell13118 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13118 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13118 ⟨51,by decide⟩).lower ∧ (cell13118 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13118 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13118 ⟨52,by decide⟩).lower ∧ (cell13118 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13118 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13118 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13118 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13118,cell13118,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13118 i).lower ∧
    (cell13118 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13118 i).upper ≤ (0.532 : ℝ) ∧
    (cell13118 i).centre ≤ (0.1 : ℝ) ∧ (cell13118 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13118 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13118 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13118

/-! The local source numeric instances at 13118 have no network premises. -/
namespace BstLean.Part269.N13118
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13118)
open BstLean.Part268 (cell13118)

noncomputable def sourceNumerics13118 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13118 (cell13118 i)
      scalarRow13118.M scalarRow13118.H scalarRow13118.xi := by
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
    energy_allowance := scalarRow13118.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13118]
    centre_nonneg := (scalarRow13118.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13118])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13118
/-! Actual 13119 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13119 ≤ (1.035227747004 : ℝ) := by
  have hr : (114.538203233680 : ℝ) ≤ √(13119 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.538203233680 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13119 13119 (11 / 1000) ≤
    (0.008345572785 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13119) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.538203233680 : ℝ) ≤ √(13119 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13119)
  have hdiv : K / √(13119 : ℝ) ≤ K / 114.538203233680 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.538203233680 ≤ (0.008345572785 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13119.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13119 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13119 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13119 := gPlus_lower 13119
end BstLean.Part269.N13119

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13119
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035227747003 : ℝ) ≤ wn 13119 := by
  have hn : √(13119 : ℝ) ≤ 114.538203233681 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13119 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.538203233681 ≤ 2 / √(13119 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243699312 : ℝ) ≤ rhoBar 13119 BstLean.Part154.csC ∧
    rhoBar 13119 BstLean.Part154.csC ≤ 0.000243699689 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035227747003 : ℝ) / (1.295212 * 13119) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035227747004 : ℝ) / (1.29521 * 13119) := by gcongr
      _ ≤ (0.000243699689 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13119 BstLean.Part154.csC) ≤ 0.000974858146 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13119 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) ≤ 0.000186139185 ∧
    cc1 (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) ≤ 0.000118441657 ∧
    cc2 (rhoBar 13119 BstLean.Part154.csC) ≤ 0.000068756360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13119 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13119 BstLean.Part154.csC * nuR (rhoBar 13119 BstLean.Part154.csC)) ≤ 0.000487414226 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243699689 : ℝ) * 0.000974858146 := by gcongr
      _ ≤ (0.000487414226 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13119 BstLean.Part154.csC) * nuR (rhoBar 13119 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974858146 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13119 BstLean.Part154.csC) * rhoBar 13119 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243699689 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243699689 / 2 + 0.399 * 0.000974858146 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186139185 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487414226 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118441657 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243699689 / 1.414213562 := by gcongr
      _ ≤ (0.000068756360 : ℝ) := by norm_num

end BstLean.Part269.N13119

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13119
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) ≤ 1.49628E-7 := by
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13119 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13119 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186139185 : ℝ) ^ 2 + 0.000118441657 ^ 2 + 3 * 0.000068756360 ^ 2 +
        2 * 0.797885 * 0.000186139185 * 0.000118441657 + 2 * 0.000186139185 * 0.000068756360 +
        4 * 0.797885 * 0.000118441657 * 0.000068756360 := by gcongr
    _ ≤ (1.49628E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13119 BstLean.Part154.csC Θ ≤ 0.002542461956 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13119 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13119 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035227747004 * 1.49628E-7 / (0.000243699312 : ℝ) := by gcongr
    _ ≤ 0.002542461956 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13119 BstLean.Part154.csC Θ ≤ 0.002819403560 + 0.000642437796 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13119 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035227747004 : ℝ) * ((2 * Θ * 0.000243699689 +
        (6863 / 10000) * 0.000243699689 * 13119 * 0.000974858146) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002819403560 + 0.000642437796 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13119 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13119 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13119 0.011 Θ ∧ gammaRatio 13119 0.011 Θ ≤ 0.000083777651 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13119 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035227747004 : ℝ) * 0.525 / ((1 - 0.011) * 13119) := by gcongr
      _ ≤ (0.000083777651 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13119 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13119 0.011 Θ) :=
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
    badAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13119 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13119 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13119 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13119 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13119 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13119 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13119 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13119 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13119 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13119 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035227747004 : ℝ) * 13119 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003168309142 + 0.003184899752 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13119

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13119
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13119 BstLean.Part154.csC) (piBar (rhoBar 13119 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13119 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13119 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13119 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13119 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13119 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13119 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13119 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13119 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13119 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051630364326 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13119) ≤ 0.010426543698 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13119 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035227747004)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010426543698 + 2 * 0.737676 / 13119) := by gcongr
    _ ≤ (0.051630364326 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13119 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13119

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13119
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521911532 : ℝ) ≤ plow 13119 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13119) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346981512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334792527) : eMP 13119 0.011 xi bn ≤ 0.001149682396 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13119 : ℝ) * (1 - 0.011))) ≤ 0.000568503748 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334792527 / (13119 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568503748 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568503748 : ℝ) + 3.141593 * 0.052346981512 / (13119 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149682396 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346981512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334792527) : PiBarMP 13119 12 0.011 xi bn ≤ 0.158629719600 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13119 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036534812536 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.906501131410 : ℝ) ≤ √((13119 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.538203233680 : ℝ) ≤ √(13119 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13119) ≤ 0.121639836050 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036534812536 + 0.052346981512 * 1.772454 / (2 * (113.906501131410 : ℝ))) * (1 + 0.001149682396) +
        8 / (13119 * 114.538203233680) + 0.121639836050 := by gcongr
    _ ≤ (0.158629719600 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346981512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334792527) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280424991693) :
    parallelOracle 13119 0.011 xi bn cd ≤ 0.159588595496 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13119 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13119 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521911532 : ℝ) ≤ plow 13119 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.538203233680 : ℝ) ≤ √(13119 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280424991693 : ℝ) / (2 * 0.560521911532 * 114.538203233680)) * 0.158629719600 +
        0.280424991693 ^ 2 / (2 * 0.560521911532 * 114.538203233680) := by gcongr
    _ ≤ (0.159588595496 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346981512) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334792527)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280424991693) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13119 13119 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521911532 : ℝ) ≤ plow 13119 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.538203233680 : ℝ) ≤ √(13119 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13119 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13119 Θ 1.22 ≤ 0.011577800792 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.538203233680 := by gcongr <;> linarith
      _ ≤ (0.011577800792 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13119 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13119 13119 0.011 ≤ 0.008345572785 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13119 13119 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13119 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13119 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13119 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13119 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159588595496 + 0.011577800792 + (0.008345572785 : ℝ) *
        (1 + 2 * (0.280424991693 + 0.011577800792) / (0.560521911532 * 114.538203233680))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13119]

end BstLean.Part269.N13119

/-! The original eight local profiles supply actual 13119 moment certificates. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13119 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052346981512 ∧
    0 ≤ bN 13119 BstLean.Part154.csC (groupTheta g) ∧ bN 13119 BstLean.Part154.csC (groupTheta g) ≤ 0.001334792527 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13119 13119 0.011
      (momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13119 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13119 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13119 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228794627367 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13119 0.011
      (momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13119 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13119
/-! The actual computed-centre upper energy formula at 13119. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13119

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13119)
open BstLean.Part268 (cell13119)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084354015727
  | 2 => 0.085278768293
  | 3 => 0.086199150310
  | 4 => 0.087115989267
  | 5 => 0.088030302895
  | 6 => 0.088943329478
  | 7 => 0.089856561409
  | 8 => 0.090771782108
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13119 13119 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13119 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13119

/-! Actual upper energy certificates on all 43 source endpoints at 13119. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13119)
open BstLean.Part268 (cell13119)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13119 (gMinus 13119) (1 - (cell13119 i).lower) ≤ 1 ∧
    energyUpper 13119 (gMinus 13119) (BstLean.Part211.gPlus 13119)
      (finiteEnergy 13119 13119 0.011) (1 - (cell13119 i).lower) ≤
      (cell13119 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨10,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨11,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨12,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨13,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨14,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨15,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨16,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨17,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨18,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨19,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨20,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨21,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨22,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨23,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨24,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨25,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨26,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨27,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨28,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨29,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨30,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨31,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨32,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨33,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨34,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨35,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨36,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨37,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨38,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨39,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨40,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨41,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨42,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨43,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨44,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨45,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨46,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨47,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨48,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨49,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨50,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨51,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13119) (by norm_num)
        (q := 1 - (cell13119 ⟨52,by decide⟩).lower)
        (by norm_num [cell13119]) (by norm_num [cell13119])
      exact ⟨E.1,E.2.trans (by norm_num [cell13119])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13119

/-! Source-cell containment and simple scalar guards at 13119. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13119)
open BstLean.Part268 (cell13119)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13119 ⟨10,by decide⟩).lower ∧ (cell13119 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13119 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13119 ⟨11,by decide⟩).lower ∧ (cell13119 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13119 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13119 ⟨12,by decide⟩).lower ∧ (cell13119 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13119 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13119 ⟨13,by decide⟩).lower ∧ (cell13119 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13119 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13119 ⟨14,by decide⟩).lower ∧ (cell13119 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13119 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13119 ⟨15,by decide⟩).lower ∧ (cell13119 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13119 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13119 ⟨16,by decide⟩).lower ∧ (cell13119 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13119 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13119 ⟨17,by decide⟩).lower ∧ (cell13119 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13119 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13119 ⟨18,by decide⟩).lower ∧ (cell13119 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13119 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13119 ⟨19,by decide⟩).lower ∧ (cell13119 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13119 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13119 ⟨20,by decide⟩).lower ∧ (cell13119 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13119 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13119 ⟨21,by decide⟩).lower ∧ (cell13119 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13119 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13119 ⟨22,by decide⟩).lower ∧ (cell13119 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13119 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13119 ⟨23,by decide⟩).lower ∧ (cell13119 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13119 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13119 ⟨24,by decide⟩).lower ∧ (cell13119 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13119 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13119 ⟨25,by decide⟩).lower ∧ (cell13119 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13119 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13119 ⟨26,by decide⟩).lower ∧ (cell13119 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13119 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13119 ⟨27,by decide⟩).lower ∧ (cell13119 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13119 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13119 ⟨28,by decide⟩).lower ∧ (cell13119 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13119 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13119 ⟨29,by decide⟩).lower ∧ (cell13119 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13119 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13119 ⟨30,by decide⟩).lower ∧ (cell13119 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13119 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13119 ⟨31,by decide⟩).lower ∧ (cell13119 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13119 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13119 ⟨32,by decide⟩).lower ∧ (cell13119 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13119 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13119 ⟨33,by decide⟩).lower ∧ (cell13119 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13119 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13119 ⟨34,by decide⟩).lower ∧ (cell13119 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13119 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13119 ⟨35,by decide⟩).lower ∧ (cell13119 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13119 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13119 ⟨36,by decide⟩).lower ∧ (cell13119 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13119 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13119 ⟨37,by decide⟩).lower ∧ (cell13119 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13119 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13119 ⟨38,by decide⟩).lower ∧ (cell13119 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13119 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13119 ⟨39,by decide⟩).lower ∧ (cell13119 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13119 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13119 ⟨40,by decide⟩).lower ∧ (cell13119 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13119 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13119 ⟨41,by decide⟩).lower ∧ (cell13119 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13119 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13119 ⟨42,by decide⟩).lower ∧ (cell13119 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13119 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13119 ⟨43,by decide⟩).lower ∧ (cell13119 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13119 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13119 ⟨44,by decide⟩).lower ∧ (cell13119 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13119 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13119 ⟨45,by decide⟩).lower ∧ (cell13119 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13119 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13119 ⟨46,by decide⟩).lower ∧ (cell13119 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13119 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13119 ⟨47,by decide⟩).lower ∧ (cell13119 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13119 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13119 ⟨48,by decide⟩).lower ∧ (cell13119 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13119 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13119 ⟨49,by decide⟩).lower ∧ (cell13119 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13119 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13119 ⟨50,by decide⟩).lower ∧ (cell13119 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13119 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13119 ⟨51,by decide⟩).lower ∧ (cell13119 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13119 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13119 ⟨52,by decide⟩).lower ∧ (cell13119 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13119 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13119 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13119 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13119,cell13119,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13119 i).lower ∧
    (cell13119 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13119 i).upper ≤ (0.532 : ℝ) ∧
    (cell13119 i).centre ≤ (0.1 : ℝ) ∧ (cell13119 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13119 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13119 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13119

/-! The local source numeric instances at 13119 have no network premises. -/
namespace BstLean.Part269.N13119
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13119)
open BstLean.Part268 (cell13119)

noncomputable def sourceNumerics13119 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13119 (cell13119 i)
      scalarRow13119.M scalarRow13119.H scalarRow13119.xi := by
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
    energy_allowance := scalarRow13119.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13119]
    centre_nonneg := (scalarRow13119.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13119])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13119
/-! Actual 13120 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13120 ≤ (1.035226392838 : ℝ) := by
  have hr : (114.542568506210 : ℝ) ≤ √(13120 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.542568506210 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13120 13120 (11 / 1000) ≤
    (0.008345254729 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13120) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.542568506210 : ℝ) ≤ √(13120 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13120)
  have hdiv : K / √(13120 : ℝ) ≤ K / 114.542568506210 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.542568506210 ≤ (0.008345254729 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13120.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13120 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13120 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13120 := gPlus_lower 13120
end BstLean.Part269.N13120

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13120
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035226392837 : ℝ) ≤ wn 13120 := by
  have hn : √(13120 : ℝ) ≤ 114.542568506211 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13120 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.542568506211 ≤ 2 / √(13120 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243680418 : ℝ) ≤ rhoBar 13120 BstLean.Part154.csC ∧
    rhoBar 13120 BstLean.Part154.csC ≤ 0.000243680796 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035226392837 : ℝ) / (1.295212 * 13120) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035226392838 : ℝ) / (1.29521 * 13120) := by gcongr
      _ ≤ (0.000243680796 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13120 BstLean.Part154.csC) ≤ 0.000974782565 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13120 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) ≤ 0.000186124754 ∧
    cc1 (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) ≤ 0.000118432475 ∧
    cc2 (rhoBar 13120 BstLean.Part154.csC) ≤ 0.000068751029 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13120 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13120 BstLean.Part154.csC * nuR (rhoBar 13120 BstLean.Part154.csC)) ≤ 0.000487376438 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243680796 : ℝ) * 0.000974782565 := by gcongr
      _ ≤ (0.000487376438 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13120 BstLean.Part154.csC) * nuR (rhoBar 13120 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974782565 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13120 BstLean.Part154.csC) * rhoBar 13120 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243680796 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243680796 / 2 + 0.399 * 0.000974782565 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186124754 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487376438 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118432475 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243680796 / 1.414213562 := by gcongr
      _ ≤ (0.000068751029 : ℝ) := by norm_num

end BstLean.Part269.N13120

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13120
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) ≤ 1.49604E-7 := by
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13120 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13120 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186124754 : ℝ) ^ 2 + 0.000118432475 ^ 2 + 3 * 0.000068751029 ^ 2 +
        2 * 0.797885 * 0.000186124754 * 0.000118432475 + 2 * 0.000186124754 * 0.000068751029 +
        4 * 0.797885 * 0.000118432475 * 0.000068751029 := by gcongr
    _ ≤ (1.49604E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13120 BstLean.Part154.csC Θ ≤ 0.002542247926 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13120 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13120 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035226392838 * 1.49604E-7 / (0.000243680418 : ℝ) := by gcongr
    _ ≤ 0.002542247926 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13120 BstLean.Part154.csC Θ ≤ 0.002819177601 + 0.000642387151 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13120 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035226392838 : ℝ) * ((2 * Θ * 0.000243680796 +
        (6863 / 10000) * 0.000243680796 * 13120 * 0.000974782565) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002819177601 + 0.000642387151 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13120 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13120 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13120 0.011 Θ ∧ gammaRatio 13120 0.011 Θ ≤ 0.000083771156 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13120 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035226392838 : ℝ) * 0.525 / ((1 - 0.011) * 13120) := by gcongr
      _ ≤ (0.000083771156 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13120 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13120 0.011 Θ) :=
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
    badAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13120 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13120 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13120 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13120 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13120 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13120 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13120 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13120 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13120 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13120 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035226392838 : ℝ) * 13120 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003168083183 + 0.003184635077 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13120

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13120
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13120 BstLean.Part154.csC) (piBar (rhoBar 13120 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13120 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13120 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13120 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13120 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13120 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13120 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13120 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13120 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13120 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051628375671 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13120) ≤ 0.010426146337 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13120 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035226392838)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010426146337 + 2 * 0.737676 / 13120) := by gcongr
    _ ≤ (0.051628375671 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13120 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13120

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13120
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521953910 : ℝ) ≤ plow 13120 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13120) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346616599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334680162) : eMP 13120 0.011 xi bn ≤ 0.001149590154 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13120 : ℝ) * (1 - 0.011))) ≤ 0.000568458154 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334680162 / (13120 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568458154 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568458154 : ℝ) + 3.141593 * 0.052346616599 / (13120 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149590154 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346616599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334680162) : PiBarMP 13120 12 0.011 xi bn ≤ 0.158623521869 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13120 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036533274724 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.910842328550 : ℝ) ≤ √((13120 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.542568506210 : ℝ) ≤ √(13120 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13120) ≤ 0.121635200297 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036533274724 + 0.052346616599 * 1.772454 / (2 * (113.910842328550 : ℝ))) * (1 + 0.001149590154) +
        8 / (13120 * 114.542568506210) + 0.121635200297 := by gcongr
    _ ≤ (0.158623521869 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346616599)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334680162) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280422205569) :
    parallelOracle 13120 0.011 xi bn cd ≤ 0.159582332003 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13120 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13120 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521953910 : ℝ) ≤ plow 13120 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.542568506210 : ℝ) ≤ √(13120 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280422205569 : ℝ) / (2 * 0.560521953910 * 114.542568506210)) * 0.158623521869 +
        0.280422205569 ^ 2 / (2 * 0.560521953910 * 114.542568506210) := by gcongr
    _ ≤ (0.159582332003 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346616599) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334680162)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280422205569) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13120 13120 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521953910 : ℝ) ≤ plow 13120 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.542568506210 : ℝ) ≤ √(13120 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13120 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13120 Θ 1.22 ≤ 0.011577359556 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.542568506210 := by gcongr <;> linarith
      _ ≤ (0.011577359556 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13120 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13120 13120 0.011 ≤ 0.008345254729 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13120 13120 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13120 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13120 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13120 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13120 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159582332003 + 0.011577359556 + (0.008345254729 : ℝ) *
        (1 + 2 * (0.280422205569 + 0.011577359556) / (0.560521953910 * 114.542568506210))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13120]

end BstLean.Part269.N13120

/-! The original eight local profiles supply actual 13120 moment certificates. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13120 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052346616599 ∧
    0 ≤ bN 13120 BstLean.Part154.csC (groupTheta g) ∧ bN 13120 BstLean.Part154.csC (groupTheta g) ≤ 0.001334680162 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13120 13120 0.011
      (momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13120 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13120 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13120 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228793829898 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13120 0.011
      (momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13120 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13120
/-! The actual computed-centre upper energy formula at 13120. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13120

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13120)
open BstLean.Part268 (cell13120)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084351488547
  | 2 => 0.085276209711
  | 3 => 0.086196555830
  | 4 => 0.087113353319
  | 5 => 0.088027618639
  | 6 => 0.088940588577
  | 7 => 0.089853753774
  | 8 => 0.090768895615
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13120 13120 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13120 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13120

/-! Actual upper energy certificates on all 43 source endpoints at 13120. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13120)
open BstLean.Part268 (cell13120)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13120 (gMinus 13120) (1 - (cell13120 i).lower) ≤ 1 ∧
    energyUpper 13120 (gMinus 13120) (BstLean.Part211.gPlus 13120)
      (finiteEnergy 13120 13120 0.011) (1 - (cell13120 i).lower) ≤
      (cell13120 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨10,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨11,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨12,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨13,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨14,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨15,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨16,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨17,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨18,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨19,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨20,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨21,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨22,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨23,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨24,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨25,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨26,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨27,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨28,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨29,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨30,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨31,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨32,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨33,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨34,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨35,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨36,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨37,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨38,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨39,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨40,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨41,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨42,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨43,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨44,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨45,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨46,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨47,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨48,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨49,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨50,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨51,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13120) (by norm_num)
        (q := 1 - (cell13120 ⟨52,by decide⟩).lower)
        (by norm_num [cell13120]) (by norm_num [cell13120])
      exact ⟨E.1,E.2.trans (by norm_num [cell13120])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13120

/-! Source-cell containment and simple scalar guards at 13120. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13120)
open BstLean.Part268 (cell13120)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13120 ⟨10,by decide⟩).lower ∧ (cell13120 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13120 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13120 ⟨11,by decide⟩).lower ∧ (cell13120 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13120 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13120 ⟨12,by decide⟩).lower ∧ (cell13120 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13120 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13120 ⟨13,by decide⟩).lower ∧ (cell13120 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13120 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13120 ⟨14,by decide⟩).lower ∧ (cell13120 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13120 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13120 ⟨15,by decide⟩).lower ∧ (cell13120 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13120 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13120 ⟨16,by decide⟩).lower ∧ (cell13120 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13120 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13120 ⟨17,by decide⟩).lower ∧ (cell13120 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13120 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13120 ⟨18,by decide⟩).lower ∧ (cell13120 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13120 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13120 ⟨19,by decide⟩).lower ∧ (cell13120 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13120 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13120 ⟨20,by decide⟩).lower ∧ (cell13120 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13120 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13120 ⟨21,by decide⟩).lower ∧ (cell13120 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13120 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13120 ⟨22,by decide⟩).lower ∧ (cell13120 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13120 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13120 ⟨23,by decide⟩).lower ∧ (cell13120 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13120 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13120 ⟨24,by decide⟩).lower ∧ (cell13120 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13120 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13120 ⟨25,by decide⟩).lower ∧ (cell13120 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13120 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13120 ⟨26,by decide⟩).lower ∧ (cell13120 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13120 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13120 ⟨27,by decide⟩).lower ∧ (cell13120 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13120 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13120 ⟨28,by decide⟩).lower ∧ (cell13120 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13120 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13120 ⟨29,by decide⟩).lower ∧ (cell13120 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13120 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13120 ⟨30,by decide⟩).lower ∧ (cell13120 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13120 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13120 ⟨31,by decide⟩).lower ∧ (cell13120 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13120 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13120 ⟨32,by decide⟩).lower ∧ (cell13120 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13120 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13120 ⟨33,by decide⟩).lower ∧ (cell13120 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13120 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13120 ⟨34,by decide⟩).lower ∧ (cell13120 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13120 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13120 ⟨35,by decide⟩).lower ∧ (cell13120 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13120 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13120 ⟨36,by decide⟩).lower ∧ (cell13120 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13120 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13120 ⟨37,by decide⟩).lower ∧ (cell13120 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13120 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13120 ⟨38,by decide⟩).lower ∧ (cell13120 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13120 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13120 ⟨39,by decide⟩).lower ∧ (cell13120 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13120 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13120 ⟨40,by decide⟩).lower ∧ (cell13120 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13120 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13120 ⟨41,by decide⟩).lower ∧ (cell13120 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13120 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13120 ⟨42,by decide⟩).lower ∧ (cell13120 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13120 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13120 ⟨43,by decide⟩).lower ∧ (cell13120 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13120 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13120 ⟨44,by decide⟩).lower ∧ (cell13120 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13120 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13120 ⟨45,by decide⟩).lower ∧ (cell13120 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13120 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13120 ⟨46,by decide⟩).lower ∧ (cell13120 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13120 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13120 ⟨47,by decide⟩).lower ∧ (cell13120 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13120 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13120 ⟨48,by decide⟩).lower ∧ (cell13120 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13120 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13120 ⟨49,by decide⟩).lower ∧ (cell13120 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13120 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13120 ⟨50,by decide⟩).lower ∧ (cell13120 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13120 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13120 ⟨51,by decide⟩).lower ∧ (cell13120 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13120 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13120 ⟨52,by decide⟩).lower ∧ (cell13120 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13120 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13120 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13120 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13120,cell13120,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13120 i).lower ∧
    (cell13120 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13120 i).upper ≤ (0.532 : ℝ) ∧
    (cell13120 i).centre ≤ (0.1 : ℝ) ∧ (cell13120 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13120 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13120 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13120

/-! The local source numeric instances at 13120 have no network premises. -/
namespace BstLean.Part269.N13120
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13120)
open BstLean.Part268 (cell13120)

noncomputable def sourceNumerics13120 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13120 (cell13120 i)
      scalarRow13120.M scalarRow13120.H scalarRow13120.xi := by
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
    energy_allowance := scalarRow13120.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13120]
    centre_nonneg := (scalarRow13120.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13120])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13120
/-! Actual 13121 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13121 ≤ (1.035225038828 : ℝ) := by
  have hr : (114.546933612384 : ℝ) ≤ √(13121 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.546933612384 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13121 13121 (11 / 1000) ≤
    (0.008344936709 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13121) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.546933612384 : ℝ) ≤ √(13121 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13121)
  have hdiv : K / √(13121 : ℝ) ≤ K / 114.546933612384 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.546933612384 ≤ (0.008344936709 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13121.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13121 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13121 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13121 := gPlus_lower 13121
end BstLean.Part269.N13121

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13121
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035225038827 : ℝ) ≤ wn 13121 := by
  have hn : √(13121 : ℝ) ≤ 114.546933612385 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13121 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.546933612385 ≤ 2 / √(13121 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243661528 : ℝ) ≤ rhoBar 13121 BstLean.Part154.csC ∧
    rhoBar 13121 BstLean.Part154.csC ≤ 0.000243661905 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035225038827 : ℝ) / (1.295212 * 13121) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035225038828 : ℝ) / (1.29521 * 13121) := by gcongr
      _ ≤ (0.000243661905 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13121 BstLean.Part154.csC) ≤ 0.000974706992 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13121 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) ≤ 0.000186110324 ∧
    cc1 (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) ≤ 0.000118423293 ∧
    cc2 (rhoBar 13121 BstLean.Part154.csC) ≤ 0.000068745700 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13121 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13121 BstLean.Part154.csC * nuR (rhoBar 13121 BstLean.Part154.csC)) ≤ 0.000487338653 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243661905 : ℝ) * 0.000974706992 := by gcongr
      _ ≤ (0.000487338653 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13121 BstLean.Part154.csC) * nuR (rhoBar 13121 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974706992 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13121 BstLean.Part154.csC) * rhoBar 13121 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243661905 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243661905 / 2 + 0.399 * 0.000974706992 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186110324 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487338653 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118423293 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243661905 / 1.414213562 := by gcongr
      _ ≤ (0.000068745700 : ℝ) := by norm_num

end BstLean.Part269.N13121

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13121
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) ≤ 1.49581E-7 := by
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13121 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13121 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186110324 : ℝ) ^ 2 + 0.000118423293 ^ 2 + 3 * 0.000068745700 ^ 2 +
        2 * 0.797885 * 0.000186110324 * 0.000118423293 + 2 * 0.000186110324 * 0.000068745700 +
        4 * 0.797885 * 0.000118423293 * 0.000068745700 := by gcongr
    _ ≤ (1.49581E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13121 BstLean.Part154.csC Θ ≤ 0.002542050817 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13121 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13121 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035225038828 * 1.49581E-7 / (0.000243661528 : ℝ) := by gcongr
    _ ≤ 0.002542050817 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13121 BstLean.Part154.csC Θ ≤ 0.002818951655 + 0.000642336510 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13121 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035225038828 : ℝ) * ((2 * Θ * 0.000243661905 +
        (6863 / 10000) * 0.000243661905 * 13121 * 0.000974706992) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002818951655 + 0.000642336510 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13121 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13121 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13121 0.011 Θ ∧ gammaRatio 13121 0.011 Θ ≤ 0.000083764662 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13121 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035225038828 : ℝ) * 0.525 / ((1 - 0.011) * 13121) := by gcongr
      _ ≤ (0.000083764662 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13121 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13121 0.011 Θ) :=
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
    badAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13121 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13121 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13121 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13121 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13121 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13121 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13121 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13121 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13121 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13121 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035225038828 : ℝ) * 13121 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003167857237 + 0.003184387327 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13121

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13121
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13121 BstLean.Part154.csC) (piBar (rhoBar 13121 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13121 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13121 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13121 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13121 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13121 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13121 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13121 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13121 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13121 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051626387247 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13121) ≤ 0.010425749022 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13121 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035225038828)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010425749022 + 2 * 0.737676 / 13121) := by gcongr
    _ ≤ (0.051626387247 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13121 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13121

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13121
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521996280 : ℝ) ≤ plow 13121 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13121) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346260584)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334576679) : eMP 13121 0.011 xi bn ≤ 0.001149501702 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13121 : ℝ) * (1 - 0.011))) ≤ 0.000568414454 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334576679 / (13121 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568414454 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568414454 : ℝ) + 3.141593 * 0.052346260584 / (13121 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149501702 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346260584)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334576679) : PiBarMP 13121 12 0.011 xi bn ≤ 0.158617446520 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13121 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036531858412 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.915183360252 : ℝ) ≤ √((13121 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.546933612384 : ℝ) ≤ √(13121 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13121) ≤ 0.121630565074 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036531858412 + 0.052346260584 * 1.772454 / (2 * (113.915183360252 : ℝ))) * (1 + 0.001149501702) +
        8 / (13121 * 114.546933612384) + 0.121630565074 := by gcongr
    _ ≤ (0.158617446520 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346260584)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334576679) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280419439118) :
    parallelOracle 13121 0.011 xi bn cd ≤ 0.159576191277 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13121 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13121 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521996280 : ℝ) ≤ plow 13121 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.546933612384 : ℝ) ≤ √(13121 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280419439118 : ℝ) / (2 * 0.560521996280 * 114.546933612384)) * 0.158617446520 +
        0.280419439118 ^ 2 / (2 * 0.560521996280 * 114.546933612384) := by gcongr
    _ ≤ (0.159576191277 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052346260584) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334576679)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280419439118) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13121 13121 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521996280 : ℝ) ≤ plow 13121 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.546933612384 : ℝ) ≤ √(13121 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13121 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13121 Θ 1.22 ≤ 0.011576918371 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.546933612384 := by gcongr <;> linarith
      _ ≤ (0.011576918371 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13121 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13121 13121 0.011 ≤ 0.008344936709 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13121 13121 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13121 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13121 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13121 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13121 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159576191277 + 0.011576918371 + (0.008344936709 : ℝ) *
        (1 + 2 * (0.280419439118 + 0.011576918371) / (0.560521996280 * 114.546933612384))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13121]

end BstLean.Part269.N13121

/-! The original eight local profiles supply actual 13121 moment certificates. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13121 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052346260584 ∧
    0 ≤ bN 13121 BstLean.Part154.csC (groupTheta g) ∧ bN 13121 BstLean.Part154.csC (groupTheta g) ≤ 0.001334576679 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13121 13121 0.011
      (momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13121 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13121 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13121 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228793051871 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13121 0.011
      (momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13121 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13121
/-! The actual computed-centre upper energy formula at 13121. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13121

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13121)
open BstLean.Part268 (cell13121)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084348962091
  | 2 => 0.085273651878
  | 3 => 0.086193962129
  | 4 => 0.087110718187
  | 5 => 0.088024935246
  | 6 => 0.088937848594
  | 7 => 0.089850947127
  | 8 => 0.090766010192
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13121 13121 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13121 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13121

/-! Actual upper energy certificates on all 43 source endpoints at 13121. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13121)
open BstLean.Part268 (cell13121)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13121 (gMinus 13121) (1 - (cell13121 i).lower) ≤ 1 ∧
    energyUpper 13121 (gMinus 13121) (BstLean.Part211.gPlus 13121)
      (finiteEnergy 13121 13121 0.011) (1 - (cell13121 i).lower) ≤
      (cell13121 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨10,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨11,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨12,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨13,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨14,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨15,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨16,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨17,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨18,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨19,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨20,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨21,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨22,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨23,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨24,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨25,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨26,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨27,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨28,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨29,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨30,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨31,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨32,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨33,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨34,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨35,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨36,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨37,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨38,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨39,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨40,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨41,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨42,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨43,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨44,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨45,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨46,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨47,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨48,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨49,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨50,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨51,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13121) (by norm_num)
        (q := 1 - (cell13121 ⟨52,by decide⟩).lower)
        (by norm_num [cell13121]) (by norm_num [cell13121])
      exact ⟨E.1,E.2.trans (by norm_num [cell13121])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13121

/-! Source-cell containment and simple scalar guards at 13121. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13121)
open BstLean.Part268 (cell13121)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13121 ⟨10,by decide⟩).lower ∧ (cell13121 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13121 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13121 ⟨11,by decide⟩).lower ∧ (cell13121 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13121 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13121 ⟨12,by decide⟩).lower ∧ (cell13121 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13121 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13121 ⟨13,by decide⟩).lower ∧ (cell13121 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13121 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13121 ⟨14,by decide⟩).lower ∧ (cell13121 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13121 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13121 ⟨15,by decide⟩).lower ∧ (cell13121 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13121 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13121 ⟨16,by decide⟩).lower ∧ (cell13121 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13121 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13121 ⟨17,by decide⟩).lower ∧ (cell13121 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13121 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13121 ⟨18,by decide⟩).lower ∧ (cell13121 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13121 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13121 ⟨19,by decide⟩).lower ∧ (cell13121 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13121 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13121 ⟨20,by decide⟩).lower ∧ (cell13121 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13121 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13121 ⟨21,by decide⟩).lower ∧ (cell13121 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13121 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13121 ⟨22,by decide⟩).lower ∧ (cell13121 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13121 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13121 ⟨23,by decide⟩).lower ∧ (cell13121 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13121 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13121 ⟨24,by decide⟩).lower ∧ (cell13121 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13121 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13121 ⟨25,by decide⟩).lower ∧ (cell13121 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13121 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13121 ⟨26,by decide⟩).lower ∧ (cell13121 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13121 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13121 ⟨27,by decide⟩).lower ∧ (cell13121 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13121 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13121 ⟨28,by decide⟩).lower ∧ (cell13121 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13121 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13121 ⟨29,by decide⟩).lower ∧ (cell13121 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13121 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13121 ⟨30,by decide⟩).lower ∧ (cell13121 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13121 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13121 ⟨31,by decide⟩).lower ∧ (cell13121 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13121 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13121 ⟨32,by decide⟩).lower ∧ (cell13121 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13121 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13121 ⟨33,by decide⟩).lower ∧ (cell13121 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13121 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13121 ⟨34,by decide⟩).lower ∧ (cell13121 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13121 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13121 ⟨35,by decide⟩).lower ∧ (cell13121 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13121 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13121 ⟨36,by decide⟩).lower ∧ (cell13121 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13121 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13121 ⟨37,by decide⟩).lower ∧ (cell13121 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13121 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13121 ⟨38,by decide⟩).lower ∧ (cell13121 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13121 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13121 ⟨39,by decide⟩).lower ∧ (cell13121 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13121 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13121 ⟨40,by decide⟩).lower ∧ (cell13121 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13121 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13121 ⟨41,by decide⟩).lower ∧ (cell13121 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13121 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13121 ⟨42,by decide⟩).lower ∧ (cell13121 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13121 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13121 ⟨43,by decide⟩).lower ∧ (cell13121 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13121 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13121 ⟨44,by decide⟩).lower ∧ (cell13121 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13121 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13121 ⟨45,by decide⟩).lower ∧ (cell13121 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13121 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13121 ⟨46,by decide⟩).lower ∧ (cell13121 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13121 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13121 ⟨47,by decide⟩).lower ∧ (cell13121 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13121 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13121 ⟨48,by decide⟩).lower ∧ (cell13121 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13121 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13121 ⟨49,by decide⟩).lower ∧ (cell13121 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13121 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13121 ⟨50,by decide⟩).lower ∧ (cell13121 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13121 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13121 ⟨51,by decide⟩).lower ∧ (cell13121 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13121 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13121 ⟨52,by decide⟩).lower ∧ (cell13121 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13121 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13121 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13121 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13121,cell13121,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13121 i).lower ∧
    (cell13121 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13121 i).upper ≤ (0.532 : ℝ) ∧
    (cell13121 i).centre ≤ (0.1 : ℝ) ∧ (cell13121 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13121 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13121 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13121

/-! The local source numeric instances at 13121 have no network premises. -/
namespace BstLean.Part269.N13121
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13121)
open BstLean.Part268 (cell13121)

noncomputable def sourceNumerics13121 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13121 (cell13121 i)
      scalarRow13121.M scalarRow13121.H scalarRow13121.xi := by
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
    energy_allowance := scalarRow13121.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13121]
    centre_nonneg := (scalarRow13121.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13121])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13121
/-! Actual 13122 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13122 ≤ (1.035223684973 : ℝ) := by
  have hr : (114.551298552220 : ℝ) ≤ √(13122 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.551298552220 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13122 13122 (11 / 1000) ≤
    (0.008344618726 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13122) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.551298552220 : ℝ) ≤ √(13122 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13122)
  have hdiv : K / √(13122 : ℝ) ≤ K / 114.551298552220 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.551298552220 ≤ (0.008344618726 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13122.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13122 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13122 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13122 := gPlus_lower 13122
end BstLean.Part269.N13122

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13122
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035223684972 : ℝ) ≤ wn 13122 := by
  have hn : √(13122 : ℝ) ≤ 114.551298552221 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13122 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.551298552221 ≤ 2 / √(13122 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243642640 : ℝ) ≤ rhoBar 13122 BstLean.Part154.csC ∧
    rhoBar 13122 BstLean.Part154.csC ≤ 0.000243643018 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035223684972 : ℝ) / (1.295212 * 13122) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035223684973 : ℝ) / (1.29521 * 13122) := by gcongr
      _ ≤ (0.000243643018 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13122 BstLean.Part154.csC) ≤ 0.000974631434 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13122 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) ≤ 0.000186095898 ∧
    cc1 (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) ≤ 0.000118414114 ∧
    cc2 (rhoBar 13122 BstLean.Part154.csC) ≤ 0.000068740371 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13122 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13122 BstLean.Part154.csC * nuR (rhoBar 13122 BstLean.Part154.csC)) ≤ 0.000487300877 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243643018 : ℝ) * 0.000974631434 := by gcongr
      _ ≤ (0.000487300877 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13122 BstLean.Part154.csC) * nuR (rhoBar 13122 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974631434 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13122 BstLean.Part154.csC) * rhoBar 13122 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243643018 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243643018 / 2 + 0.399 * 0.000974631434 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186095898 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487300877 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118414114 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243643018 / 1.414213562 := by gcongr
      _ ≤ (0.000068740371 : ℝ) := by norm_num

end BstLean.Part269.N13122

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13122
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) ≤ 1.49558E-7 := by
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13122 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13122 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186095898 : ℝ) ^ 2 + 0.000118414114 ^ 2 + 3 * 0.000068740371 ^ 2 +
        2 * 0.797885 * 0.000186095898 * 0.000118414114 + 2 * 0.000186095898 * 0.000068740371 +
        4 * 0.797885 * 0.000118414114 * 0.000068740371 := by gcongr
    _ ≤ (1.49558E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13122 BstLean.Part154.csC Θ ≤ 0.002541853658 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13122 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13122 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035223684973 * 1.49558E-7 / (0.000243642640 : ℝ) := by gcongr
    _ ≤ 0.002541853658 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13122 BstLean.Part154.csC Θ ≤ 0.002818725768 + 0.000642285881 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13122 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035223684973 : ℝ) * ((2 * Θ * 0.000243643018 +
        (6863 / 10000) * 0.000243643018 * 13122 * 0.000974631434) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002818725768 + 0.000642285881 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13122 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13122 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13122 0.011 Θ ∧ gammaRatio 13122 0.011 Θ ≤ 0.000083758169 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13122 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035223684973 : ℝ) * 0.525 / ((1 - 0.011) * 13122) := by gcongr
      _ ≤ (0.000083758169 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13122 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13122 0.011 Θ) :=
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
    badAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13122 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13122 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13122 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13122 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13122 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13122 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13122 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13122 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13122 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13122 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035223684973 : ℝ) * 13122 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003167631350 + 0.003184139539 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13122

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13122
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13122 BstLean.Part154.csC) (piBar (rhoBar 13122 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13122 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13122 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13122 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13122 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13122 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13122 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13122 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13122 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13122 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051624399050 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13122) ≤ 0.010425351752 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13122 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035223684973)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010425351752 + 2 * 0.737676 / 13122) := by gcongr
    _ ≤ (0.051624399050 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13122 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13122

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13122
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522038645 : ℝ) ≤ plow 13122 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13122) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345904608)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334473171) : eMP 13122 0.011 xi bn ≤ 0.001149413246 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13122 : ℝ) * (1 - 0.011))) ≤ 0.000568370752 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334473171 / (13122 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568370752 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568370752 : ℝ) + 3.141593 * 0.052345904608 / (13122 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149413246 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345904608)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334473171) : PiBarMP 13122 12 0.011 xi bn ≤ 0.158611371305 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13122 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036530441703 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.919524226534 : ℝ) ≤ √((13122 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.551298552220 : ℝ) ≤ √(13122 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13122) ≤ 0.121625930381 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036530441703 + 0.052345904608 * 1.772454 / (2 * (113.919524226534 : ℝ))) * (1 + 0.001149413246) +
        8 / (13122 * 114.551298552220) + 0.121625930381 := by gcongr
    _ ≤ (0.158611371305 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345904608)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334473171) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280416672976) :
    parallelOracle 13122 0.011 xi bn cd ≤ 0.159570050694 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13122 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13122 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522038645 : ℝ) ≤ plow 13122 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.551298552220 : ℝ) ≤ √(13122 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280416672976 : ℝ) / (2 * 0.560522038645 * 114.551298552220)) * 0.158611371305 +
        0.280416672976 ^ 2 / (2 * 0.560522038645 * 114.551298552220) := by gcongr
    _ ≤ (0.159570050694 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345904608) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334473171)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280416672976) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13122 13122 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522038645 : ℝ) ≤ plow 13122 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.551298552220 : ℝ) ≤ √(13122 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13122 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13122 Θ 1.22 ≤ 0.011576477236 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.551298552220 := by gcongr <;> linarith
      _ ≤ (0.011576477236 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13122 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13122 13122 0.011 ≤ 0.008344618726 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13122 13122 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13122 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13122 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13122 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13122 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159570050694 + 0.011576477236 + (0.008344618726 : ℝ) *
        (1 + 2 * (0.280416672976 + 0.011576477236) / (0.560522038645 * 114.551298552220))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13122]

end BstLean.Part269.N13122

/-! The original eight local profiles supply actual 13122 moment certificates. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13122 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052345904608 ∧
    0 ≤ bN 13122 BstLean.Part154.csC (groupTheta g) ∧ bN 13122 BstLean.Part154.csC (groupTheta g) ≤ 0.001334473171 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13122 13122 0.011
      (momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13122 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13122 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13122 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228792273926 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13122 0.011
      (momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13122 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13122
/-! The actual computed-centre upper energy formula at 13122. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13122

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13122)
open BstLean.Part268 (cell13122)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084346436360
  | 2 => 0.085271094794
  | 3 => 0.086191369206
  | 4 => 0.087108083872
  | 5 => 0.088022252714
  | 6 => 0.088935109531
  | 7 => 0.089848141467
  | 8 => 0.090763125839
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13122 13122 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13122 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13122

/-! Actual upper energy certificates on all 43 source endpoints at 13122. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13122)
open BstLean.Part268 (cell13122)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13122 (gMinus 13122) (1 - (cell13122 i).lower) ≤ 1 ∧
    energyUpper 13122 (gMinus 13122) (BstLean.Part211.gPlus 13122)
      (finiteEnergy 13122 13122 0.011) (1 - (cell13122 i).lower) ≤
      (cell13122 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨10,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨11,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨12,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨13,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨14,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨15,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨16,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨17,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨18,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨19,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨20,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨21,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨22,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨23,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨24,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨25,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨26,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨27,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨28,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨29,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨30,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨31,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨32,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨33,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨34,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨35,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨36,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨37,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨38,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨39,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨40,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨41,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨42,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨43,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨44,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨45,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨46,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨47,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨48,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨49,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨50,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨51,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13122) (by norm_num)
        (q := 1 - (cell13122 ⟨52,by decide⟩).lower)
        (by norm_num [cell13122]) (by norm_num [cell13122])
      exact ⟨E.1,E.2.trans (by norm_num [cell13122])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13122

/-! Source-cell containment and simple scalar guards at 13122. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13122)
open BstLean.Part268 (cell13122)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13122 ⟨10,by decide⟩).lower ∧ (cell13122 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13122 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13122 ⟨11,by decide⟩).lower ∧ (cell13122 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13122 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13122 ⟨12,by decide⟩).lower ∧ (cell13122 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13122 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13122 ⟨13,by decide⟩).lower ∧ (cell13122 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13122 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13122 ⟨14,by decide⟩).lower ∧ (cell13122 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13122 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13122 ⟨15,by decide⟩).lower ∧ (cell13122 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13122 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13122 ⟨16,by decide⟩).lower ∧ (cell13122 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13122 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13122 ⟨17,by decide⟩).lower ∧ (cell13122 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13122 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13122 ⟨18,by decide⟩).lower ∧ (cell13122 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13122 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13122 ⟨19,by decide⟩).lower ∧ (cell13122 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13122 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13122 ⟨20,by decide⟩).lower ∧ (cell13122 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13122 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13122 ⟨21,by decide⟩).lower ∧ (cell13122 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13122 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13122 ⟨22,by decide⟩).lower ∧ (cell13122 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13122 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13122 ⟨23,by decide⟩).lower ∧ (cell13122 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13122 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13122 ⟨24,by decide⟩).lower ∧ (cell13122 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13122 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13122 ⟨25,by decide⟩).lower ∧ (cell13122 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13122 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13122 ⟨26,by decide⟩).lower ∧ (cell13122 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13122 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13122 ⟨27,by decide⟩).lower ∧ (cell13122 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13122 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13122 ⟨28,by decide⟩).lower ∧ (cell13122 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13122 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13122 ⟨29,by decide⟩).lower ∧ (cell13122 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13122 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13122 ⟨30,by decide⟩).lower ∧ (cell13122 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13122 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13122 ⟨31,by decide⟩).lower ∧ (cell13122 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13122 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13122 ⟨32,by decide⟩).lower ∧ (cell13122 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13122 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13122 ⟨33,by decide⟩).lower ∧ (cell13122 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13122 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13122 ⟨34,by decide⟩).lower ∧ (cell13122 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13122 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13122 ⟨35,by decide⟩).lower ∧ (cell13122 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13122 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13122 ⟨36,by decide⟩).lower ∧ (cell13122 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13122 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13122 ⟨37,by decide⟩).lower ∧ (cell13122 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13122 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13122 ⟨38,by decide⟩).lower ∧ (cell13122 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13122 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13122 ⟨39,by decide⟩).lower ∧ (cell13122 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13122 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13122 ⟨40,by decide⟩).lower ∧ (cell13122 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13122 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13122 ⟨41,by decide⟩).lower ∧ (cell13122 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13122 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13122 ⟨42,by decide⟩).lower ∧ (cell13122 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13122 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13122 ⟨43,by decide⟩).lower ∧ (cell13122 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13122 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13122 ⟨44,by decide⟩).lower ∧ (cell13122 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13122 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13122 ⟨45,by decide⟩).lower ∧ (cell13122 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13122 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13122 ⟨46,by decide⟩).lower ∧ (cell13122 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13122 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13122 ⟨47,by decide⟩).lower ∧ (cell13122 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13122 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13122 ⟨48,by decide⟩).lower ∧ (cell13122 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13122 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13122 ⟨49,by decide⟩).lower ∧ (cell13122 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13122 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13122 ⟨50,by decide⟩).lower ∧ (cell13122 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13122 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13122 ⟨51,by decide⟩).lower ∧ (cell13122 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13122 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13122 ⟨52,by decide⟩).lower ∧ (cell13122 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13122 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13122 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13122 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13122,cell13122,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13122 i).lower ∧
    (cell13122 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13122 i).upper ≤ (0.532 : ℝ) ∧
    (cell13122 i).centre ≤ (0.1 : ℝ) ∧ (cell13122 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13122 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13122 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13122

/-! The local source numeric instances at 13122 have no network premises. -/
namespace BstLean.Part269.N13122
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13122)
open BstLean.Part268 (cell13122)

noncomputable def sourceNumerics13122 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13122 (cell13122 i)
      scalarRow13122.M scalarRow13122.H scalarRow13122.xi := by
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
    energy_allowance := scalarRow13122.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13122]
    centre_nonneg := (scalarRow13122.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13122])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13122
/-! Actual 13123 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13123 ≤ (1.035222331274 : ℝ) := by
  have hr : (114.555663325738 : ℝ) ≤ √(13123 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.555663325738 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13123 13123 (11 / 1000) ≤
    (0.008344300778 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13123) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.555663325738 : ℝ) ≤ √(13123 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13123)
  have hdiv : K / √(13123 : ℝ) ≤ K / 114.555663325738 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.555663325738 ≤ (0.008344300778 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13123.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13123 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13123 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13123 := gPlus_lower 13123
end BstLean.Part269.N13123

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13123
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035222331273 : ℝ) ≤ wn 13123 := by
  have hn : √(13123 : ℝ) ≤ 114.555663325739 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13123 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.555663325739 ≤ 2 / √(13123 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243623756 : ℝ) ≤ rhoBar 13123 BstLean.Part154.csC ∧
    rhoBar 13123 BstLean.Part154.csC ≤ 0.000243624133 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035222331273 : ℝ) / (1.295212 * 13123) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035222331274 : ℝ) / (1.29521 * 13123) := by gcongr
      _ ≤ (0.000243624133 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13123 BstLean.Part154.csC) ≤ 0.000974555885 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13123 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) ≤ 0.000186081473 ∧
    cc1 (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) ≤ 0.000118404935 ∧
    cc2 (rhoBar 13123 BstLean.Part154.csC) ≤ 0.000068735043 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13123 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13123 BstLean.Part154.csC * nuR (rhoBar 13123 BstLean.Part154.csC)) ≤ 0.000487263105 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243624133 : ℝ) * 0.000974555885 := by gcongr
      _ ≤ (0.000487263105 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13123 BstLean.Part154.csC) * nuR (rhoBar 13123 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974555885 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13123 BstLean.Part154.csC) * rhoBar 13123 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243624133 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243624133 / 2 + 0.399 * 0.000974555885 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186081473 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487263105 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118404935 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243624133 / 1.414213562 := by gcongr
      _ ≤ (0.000068735043 : ℝ) := by norm_num

end BstLean.Part269.N13123

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13123
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) ≤ 1.49535E-7 := by
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13123 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13123 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186081473 : ℝ) ^ 2 + 0.000118404935 ^ 2 + 3 * 0.000068735043 ^ 2 +
        2 * 0.797885 * 0.000186081473 * 0.000118404935 + 2 * 0.000186081473 * 0.000068735043 +
        4 * 0.797885 * 0.000118404935 * 0.000068735043 := by gcongr
    _ ≤ (1.49535E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13123 BstLean.Part154.csC Θ ≤ 0.002541656428 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13123 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13123 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035222331274 * 1.49535E-7 / (0.000243623756 : ℝ) := by gcongr
    _ ≤ 0.002541656428 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13123 BstLean.Part154.csC Θ ≤ 0.002818499899 + 0.000642235257 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13123 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035222331274 : ℝ) * ((2 * Θ * 0.000243624133 +
        (6863 / 10000) * 0.000243624133 * 13123 * 0.000974555885) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002818499899 + 0.000642235257 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13123 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13123 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13123 0.011 Θ ∧ gammaRatio 13123 0.011 Θ ≤ 0.000083751677 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13123 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035222331274 : ℝ) * 0.525 / ((1 - 0.011) * 13123) := by gcongr
      _ ≤ (0.000083751677 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13123 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13123 0.011 Θ) :=
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
    badAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13123 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13123 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13123 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13123 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13123 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13123 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13123 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13123 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13123 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13123 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035222331274 : ℝ) * 13123 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003167405481 + 0.003183891685 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13123

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13123
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13123 BstLean.Part154.csC) (piBar (rhoBar 13123 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13123 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13123 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13123 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13123 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13123 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13123 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13123 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13123 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13123 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051622411085 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13123) ≤ 0.010424954528 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13123 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035222331274)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010424954528 + 2 * 0.737676 / 13123) := by gcongr
    _ ≤ (0.051622411085 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13123 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13123

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13123
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522081002 : ℝ) ≤ plow 13123 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13123) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345548616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334369625) : eMP 13123 0.011 xi bn ≤ 0.001149324782 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13123 : ℝ) * (1 - 0.011))) ≤ 0.000568327046 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334369625 / (13123 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568327046 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568327046 : ℝ) + 3.141593 * 0.052345548616 / (13123 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149324782 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345548616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334369625) : PiBarMP 13123 12 0.011 xi bn ≤ 0.158605296047 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13123 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036529024419 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.923864927415 : ℝ) ≤ √((13123 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.555663325738 : ℝ) ≤ √(13123 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13123) ≤ 0.121621296218 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036529024419 + 0.052345548616 * 1.772454 / (2 * (113.923864927415 : ℝ))) * (1 + 0.001149324782) +
        8 / (13123 * 114.555663325738) + 0.121621296218 := by gcongr
    _ ≤ (0.158605296047 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345548616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334369625) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280413907029) :
    parallelOracle 13123 0.011 xi bn cd ≤ 0.159563910075 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13123 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13123 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522081002 : ℝ) ≤ plow 13123 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.555663325738 : ℝ) ≤ √(13123 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280413907029 : ℝ) / (2 * 0.560522081002 * 114.555663325738)) * 0.158605296047 +
        0.280413907029 ^ 2 / (2 * 0.560522081002 * 114.555663325738) := by gcongr
    _ ≤ (0.159563910075 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345548616) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334369625)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280413907029) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13123 13123 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522081002 : ℝ) ≤ plow 13123 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.555663325738 : ℝ) ≤ √(13123 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13123 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13123 Θ 1.22 ≤ 0.011576036152 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.555663325738 := by gcongr <;> linarith
      _ ≤ (0.011576036152 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13123 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13123 13123 0.011 ≤ 0.008344300778 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13123 13123 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13123 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13123 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13123 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13123 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159563910075 + 0.011576036152 + (0.008344300778 : ℝ) *
        (1 + 2 * (0.280413907029 + 0.011576036152) / (0.560522081002 * 114.555663325738))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13123]

end BstLean.Part269.N13123

/-! The original eight local profiles supply actual 13123 moment certificates. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13123 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052345548616 ∧
    0 ≤ bN 13123 BstLean.Part154.csC (groupTheta g) ∧ bN 13123 BstLean.Part154.csC (groupTheta g) ≤ 0.001334369625 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13123 13123 0.011
      (momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13123 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13123 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13123 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228791495944 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13123 0.011
      (momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13123 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13123
/-! The actual computed-centre upper energy formula at 13123. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13123

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13123)
open BstLean.Part268 (cell13123)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084343911351
  | 2 => 0.085268538457
  | 3 => 0.086188777061
  | 4 => 0.087105450372
  | 5 => 0.088019571044
  | 6 => 0.088932371385
  | 7 => 0.089845336793
  | 8 => 0.090760242555
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13123 13123 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13123 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13123

/-! Actual upper energy certificates on all 43 source endpoints at 13123. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13123)
open BstLean.Part268 (cell13123)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13123 (gMinus 13123) (1 - (cell13123 i).lower) ≤ 1 ∧
    energyUpper 13123 (gMinus 13123) (BstLean.Part211.gPlus 13123)
      (finiteEnergy 13123 13123 0.011) (1 - (cell13123 i).lower) ≤
      (cell13123 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨10,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨11,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨12,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨13,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨14,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨15,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨16,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨17,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨18,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨19,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨20,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨21,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨22,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨23,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨24,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨25,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨26,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨27,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨28,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨29,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨30,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨31,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨32,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨33,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨34,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨35,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨36,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨37,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨38,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨39,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨40,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨41,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨42,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨43,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨44,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨45,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨46,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨47,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨48,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨49,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨50,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨51,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13123) (by norm_num)
        (q := 1 - (cell13123 ⟨52,by decide⟩).lower)
        (by norm_num [cell13123]) (by norm_num [cell13123])
      exact ⟨E.1,E.2.trans (by norm_num [cell13123])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13123

/-! Source-cell containment and simple scalar guards at 13123. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13123)
open BstLean.Part268 (cell13123)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13123 ⟨10,by decide⟩).lower ∧ (cell13123 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13123 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13123 ⟨11,by decide⟩).lower ∧ (cell13123 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13123 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13123 ⟨12,by decide⟩).lower ∧ (cell13123 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13123 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13123 ⟨13,by decide⟩).lower ∧ (cell13123 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13123 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13123 ⟨14,by decide⟩).lower ∧ (cell13123 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13123 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13123 ⟨15,by decide⟩).lower ∧ (cell13123 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13123 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13123 ⟨16,by decide⟩).lower ∧ (cell13123 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13123 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13123 ⟨17,by decide⟩).lower ∧ (cell13123 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13123 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13123 ⟨18,by decide⟩).lower ∧ (cell13123 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13123 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13123 ⟨19,by decide⟩).lower ∧ (cell13123 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13123 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13123 ⟨20,by decide⟩).lower ∧ (cell13123 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13123 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13123 ⟨21,by decide⟩).lower ∧ (cell13123 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13123 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13123 ⟨22,by decide⟩).lower ∧ (cell13123 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13123 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13123 ⟨23,by decide⟩).lower ∧ (cell13123 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13123 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13123 ⟨24,by decide⟩).lower ∧ (cell13123 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13123 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13123 ⟨25,by decide⟩).lower ∧ (cell13123 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13123 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13123 ⟨26,by decide⟩).lower ∧ (cell13123 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13123 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13123 ⟨27,by decide⟩).lower ∧ (cell13123 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13123 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13123 ⟨28,by decide⟩).lower ∧ (cell13123 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13123 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13123 ⟨29,by decide⟩).lower ∧ (cell13123 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13123 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13123 ⟨30,by decide⟩).lower ∧ (cell13123 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13123 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13123 ⟨31,by decide⟩).lower ∧ (cell13123 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13123 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13123 ⟨32,by decide⟩).lower ∧ (cell13123 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13123 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13123 ⟨33,by decide⟩).lower ∧ (cell13123 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13123 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13123 ⟨34,by decide⟩).lower ∧ (cell13123 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13123 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13123 ⟨35,by decide⟩).lower ∧ (cell13123 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13123 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13123 ⟨36,by decide⟩).lower ∧ (cell13123 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13123 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13123 ⟨37,by decide⟩).lower ∧ (cell13123 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13123 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13123 ⟨38,by decide⟩).lower ∧ (cell13123 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13123 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13123 ⟨39,by decide⟩).lower ∧ (cell13123 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13123 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13123 ⟨40,by decide⟩).lower ∧ (cell13123 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13123 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13123 ⟨41,by decide⟩).lower ∧ (cell13123 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13123 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13123 ⟨42,by decide⟩).lower ∧ (cell13123 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13123 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13123 ⟨43,by decide⟩).lower ∧ (cell13123 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13123 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13123 ⟨44,by decide⟩).lower ∧ (cell13123 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13123 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13123 ⟨45,by decide⟩).lower ∧ (cell13123 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13123 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13123 ⟨46,by decide⟩).lower ∧ (cell13123 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13123 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13123 ⟨47,by decide⟩).lower ∧ (cell13123 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13123 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13123 ⟨48,by decide⟩).lower ∧ (cell13123 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13123 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13123 ⟨49,by decide⟩).lower ∧ (cell13123 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13123 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13123 ⟨50,by decide⟩).lower ∧ (cell13123 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13123 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13123 ⟨51,by decide⟩).lower ∧ (cell13123 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13123 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13123 ⟨52,by decide⟩).lower ∧ (cell13123 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13123 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13123 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13123 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13123,cell13123,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13123 i).lower ∧
    (cell13123 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13123 i).upper ≤ (0.532 : ℝ) ∧
    (cell13123 i).centre ≤ (0.1 : ℝ) ∧ (cell13123 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13123 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13123 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13123

/-! The local source numeric instances at 13123 have no network premises. -/
namespace BstLean.Part269.N13123
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13123)
open BstLean.Part268 (cell13123)

noncomputable def sourceNumerics13123 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13123 (cell13123 i)
      scalarRow13123.M scalarRow13123.H scalarRow13123.xi := by
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
    energy_allowance := scalarRow13123.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13123]
    centre_nonneg := (scalarRow13123.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13123])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13123
/-! Actual 13124 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13124 ≤ (1.035220977731 : ℝ) := by
  have hr : (114.560027932957 : ℝ) ≤ √(13124 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.560027932957 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13124 13124 (11 / 1000) ≤
    (0.008343982868 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13124) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.560027932957 : ℝ) ≤ √(13124 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13124)
  have hdiv : K / √(13124 : ℝ) ≤ K / 114.560027932957 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.560027932957 ≤ (0.008343982868 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13124.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13124 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13124 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13124 := gPlus_lower 13124
end BstLean.Part269.N13124

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13124
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035220977730 : ℝ) ≤ wn 13124 := by
  have hn : √(13124 : ℝ) ≤ 114.560027932958 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13124 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.560027932958 ≤ 2 / √(13124 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243604874 : ℝ) ≤ rhoBar 13124 BstLean.Part154.csC ∧
    rhoBar 13124 BstLean.Part154.csC ≤ 0.000243605251 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035220977730 : ℝ) / (1.295212 * 13124) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035220977731 : ℝ) / (1.29521 * 13124) := by gcongr
      _ ≤ (0.000243605251 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13124 BstLean.Part154.csC) ≤ 0.000974480348 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13124 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) ≤ 0.000186067050 ∧
    cc1 (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) ≤ 0.000118395758 ∧
    cc2 (rhoBar 13124 BstLean.Part154.csC) ≤ 0.000068729716 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13124 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13124 BstLean.Part154.csC * nuR (rhoBar 13124 BstLean.Part154.csC)) ≤ 0.000487225338 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243605251 : ℝ) * 0.000974480348 := by gcongr
      _ ≤ (0.000487225338 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13124 BstLean.Part154.csC) * nuR (rhoBar 13124 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974480348 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13124 BstLean.Part154.csC) * rhoBar 13124 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243605251 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243605251 / 2 + 0.399 * 0.000974480348 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186067050 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487225338 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118395758 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243605251 / 1.414213562 := by gcongr
      _ ≤ (0.000068729716 : ℝ) := by norm_num

end BstLean.Part269.N13124

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13124
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) ≤ 1.49512E-7 := by
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13124 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13124 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186067050 : ℝ) ^ 2 + 0.000118395758 ^ 2 + 3 * 0.000068729716 ^ 2 +
        2 * 0.797885 * 0.000186067050 * 0.000118395758 + 2 * 0.000186067050 * 0.000068729716 +
        4 * 0.797885 * 0.000118395758 * 0.000068729716 := by gcongr
    _ ≤ (1.49512E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13124 BstLean.Part154.csC Θ ≤ 0.002541459148 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13124 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13124 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035220977731 * 1.49512E-7 / (0.000243604874 : ℝ) := by gcongr
    _ ≤ 0.002541459148 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13124 BstLean.Part154.csC Θ ≤ 0.002818274067 + 0.000642184641 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13124 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035220977731 : ℝ) * ((2 * Θ * 0.000243605251 +
        (6863 / 10000) * 0.000243605251 * 13124 * 0.000974480348) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002818274067 + 0.000642184641 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13124 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13124 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13124 0.011 Θ ∧ gammaRatio 13124 0.011 Θ ≤ 0.000083745186 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13124 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035220977731 : ℝ) * 0.525 / ((1 - 0.011) * 13124) := by gcongr
      _ ≤ (0.000083745186 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13124 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13124 0.011 Θ) :=
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
    badAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348905582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13124 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13124 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13124 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13124 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13124 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13124 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13124 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13124 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13124 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13124 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035220977731 : ℝ) * 13124 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348905582 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003167179649 + 0.003183643789 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13124

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13124
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13124 BstLean.Part154.csC) (piBar (rhoBar 13124 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13124 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13124 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13124 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13124 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13124 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13124 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13124 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13124 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13124 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051620423346 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13124) ≤ 0.010424557349 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13124 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035220977731)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010424557349 + 2 * 0.737676 / 13124) := by gcongr
    _ ≤ (0.051620423346 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13124 12 ≤ 0.0015 := by
  exact BstLean.Part269.S30.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13124

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13124
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522123354 : ℝ) ≤ plow 13124 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13124) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345192639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334266053) : eMP 13124 0.011 xi bn ≤ 0.001149236313 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13124 : ℝ) * (1 - 0.011))) ≤ 0.000568283337 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334266053 / (13124 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568283337 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568283337 : ℝ) + 3.141593 * 0.052345192639 / (13124 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149236313 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345192639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334266053) : PiBarMP 13124 12 0.011 xi bn ≤ 0.158599220911 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13124 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036527606725 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.928205462914 : ℝ) ≤ √((13124 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.560027932957 : ℝ) ≤ √(13124 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13124) ≤ 0.121616662585 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036527606725 + 0.052345192639 * 1.772454 / (2 * (113.928205462914 : ℝ))) * (1 + 0.001149236313) +
        8 / (13124 * 114.560027932957) + 0.121616662585 := by gcongr
    _ ≤ (0.158599220911 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345192639)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334266053) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280411141338) :
    parallelOracle 13124 0.011 xi bn cd ≤ 0.159557769587 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13124 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13124 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522123354 : ℝ) ≤ plow 13124 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.560027932957 : ℝ) ≤ √(13124 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280411141338 : ℝ) / (2 * 0.560522123354 * 114.560027932957)) * 0.158599220911 +
        0.280411141338 ^ 2 / (2 * 0.560522123354 * 114.560027932957) := by gcongr
    _ ≤ (0.159557769587 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345192639) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334266053)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280411141338) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13124 13124 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522123354 : ℝ) ≤ plow 13124 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.560027932957 : ℝ) ≤ √(13124 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13124 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13124 Θ 1.22 ≤ 0.011575595118 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.560027932957 := by gcongr <;> linarith
      _ ≤ (0.011575595118 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13124 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13124 13124 0.011 ≤ 0.008343982868 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13124 13124 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13124 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13124 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13124 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13124 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159557769587 + 0.011575595118 + (0.008343982868 : ℝ) *
        (1 + 2 * (0.280411141338 + 0.011575595118) / (0.560522123354 * 114.560027932957))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13124]

end BstLean.Part269.N13124

/-! The original eight local profiles supply actual 13124 moment certificates. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13124 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052345192639 ∧
    0 ≤ bN 13124 BstLean.Part154.csC (groupTheta g) ∧ bN 13124 BstLean.Part154.csC (groupTheta g) ≤ 0.001334266053 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13124 13124 0.011
      (momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13124 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13124 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13124 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228790717992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13124 0.011
      (momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13124 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13124
/-! The actual computed-centre upper energy formula at 13124. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13124

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13124)
open BstLean.Part268 (cell13124)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084341387065
  | 2 => 0.085265982867
  | 3 => 0.086186185694
  | 4 => 0.087102817686
  | 5 => 0.088016890234
  | 6 => 0.088929634155
  | 7 => 0.089842533103
  | 8 => 0.090757360338
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13124 13124 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13124 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003172609372 + 0.003189663925 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S30.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S30.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13124

/-! Actual upper energy certificates on all 43 source endpoints at 13124. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13124)
open BstLean.Part268 (cell13124)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13124 (gMinus 13124) (1 - (cell13124 i).lower) ≤ 1 ∧
    energyUpper 13124 (gMinus 13124) (BstLean.Part211.gPlus 13124)
      (finiteEnergy 13124 13124 0.011) (1 - (cell13124 i).lower) ≤
      (cell13124 i).energy := by
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
      have E := BstLean.Part269.S30.uniformEnergy10 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨10,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy11 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨11,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy12 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨12,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy13 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨13,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy14 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨14,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy15 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨15,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy16 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨16,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy17 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨17,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy18 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨18,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy19 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨19,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy20 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨20,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy21 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨21,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy22 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨22,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy23 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨23,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy24 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨24,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy25 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨25,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy26 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨26,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy27 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨27,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy28 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨28,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy29 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨29,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy30 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨30,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy31 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨31,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy32 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨32,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy33 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨33,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy34 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨34,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy35 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨35,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy36 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨36,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy37 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨37,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy38 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨38,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy39 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨39,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy40 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨40,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy41 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨41,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy42 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨42,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy43 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨43,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy44 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨44,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy45 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨45,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy46 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨46,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy47 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨47,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy48 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨48,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy49 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨49,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy50 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨50,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy51 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨51,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S30.uniformEnergy52 (n := 13124) (by norm_num)
        (q := 1 - (cell13124 ⟨52,by decide⟩).lower)
        (by norm_num [cell13124]) (by norm_num [cell13124])
      exact ⟨E.1,E.2.trans (by norm_num [cell13124])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13124

/-! Source-cell containment and simple scalar guards at 13124. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13124)
open BstLean.Part268 (cell13124)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13124 ⟨10,by decide⟩).lower ∧ (cell13124 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13124 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13124 ⟨11,by decide⟩).lower ∧ (cell13124 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13124 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13124 ⟨12,by decide⟩).lower ∧ (cell13124 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13124 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13124 ⟨13,by decide⟩).lower ∧ (cell13124 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13124 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13124 ⟨14,by decide⟩).lower ∧ (cell13124 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13124 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13124 ⟨15,by decide⟩).lower ∧ (cell13124 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13124 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13124 ⟨16,by decide⟩).lower ∧ (cell13124 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13124 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13124 ⟨17,by decide⟩).lower ∧ (cell13124 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13124 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13124 ⟨18,by decide⟩).lower ∧ (cell13124 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13124 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13124 ⟨19,by decide⟩).lower ∧ (cell13124 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13124 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13124 ⟨20,by decide⟩).lower ∧ (cell13124 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13124 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13124 ⟨21,by decide⟩).lower ∧ (cell13124 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13124 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13124 ⟨22,by decide⟩).lower ∧ (cell13124 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13124 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13124 ⟨23,by decide⟩).lower ∧ (cell13124 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13124 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13124 ⟨24,by decide⟩).lower ∧ (cell13124 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13124 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13124 ⟨25,by decide⟩).lower ∧ (cell13124 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13124 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13124 ⟨26,by decide⟩).lower ∧ (cell13124 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13124 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13124 ⟨27,by decide⟩).lower ∧ (cell13124 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13124 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13124 ⟨28,by decide⟩).lower ∧ (cell13124 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13124 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13124 ⟨29,by decide⟩).lower ∧ (cell13124 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13124 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13124 ⟨30,by decide⟩).lower ∧ (cell13124 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13124 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13124 ⟨31,by decide⟩).lower ∧ (cell13124 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13124 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13124 ⟨32,by decide⟩).lower ∧ (cell13124 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13124 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13124 ⟨33,by decide⟩).lower ∧ (cell13124 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13124 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13124 ⟨34,by decide⟩).lower ∧ (cell13124 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13124 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13124 ⟨35,by decide⟩).lower ∧ (cell13124 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13124 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13124 ⟨36,by decide⟩).lower ∧ (cell13124 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13124 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13124 ⟨37,by decide⟩).lower ∧ (cell13124 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13124 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13124 ⟨38,by decide⟩).lower ∧ (cell13124 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13124 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13124 ⟨39,by decide⟩).lower ∧ (cell13124 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13124 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13124 ⟨40,by decide⟩).lower ∧ (cell13124 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13124 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13124 ⟨41,by decide⟩).lower ∧ (cell13124 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13124 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13124 ⟨42,by decide⟩).lower ∧ (cell13124 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13124 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13124 ⟨43,by decide⟩).lower ∧ (cell13124 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13124 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13124 ⟨44,by decide⟩).lower ∧ (cell13124 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13124 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13124 ⟨45,by decide⟩).lower ∧ (cell13124 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13124 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13124 ⟨46,by decide⟩).lower ∧ (cell13124 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13124 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13124 ⟨47,by decide⟩).lower ∧ (cell13124 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13124 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13124 ⟨48,by decide⟩).lower ∧ (cell13124 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13124 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13124 ⟨49,by decide⟩).lower ∧ (cell13124 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13124 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13124 ⟨50,by decide⟩).lower ∧ (cell13124 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13124 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13124 ⟨51,by decide⟩).lower ∧ (cell13124 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13124 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13124 ⟨52,by decide⟩).lower ∧ (cell13124 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13124 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13124 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13124 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13124,cell13124,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13124 i).lower ∧
    (cell13124 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13124 i).upper ≤ (0.532 : ℝ) ∧
    (cell13124 i).centre ≤ (0.1 : ℝ) ∧ (cell13124 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13124 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13124 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13124

/-! The local source numeric instances at 13124 have no network premises. -/
namespace BstLean.Part269.N13124
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13124)
open BstLean.Part268 (cell13124)

noncomputable def sourceNumerics13124 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13124 (cell13124 i)
      scalarRow13124.M scalarRow13124.H scalarRow13124.xi := by
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
    energy_allowance := scalarRow13124.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13124]
    centre_nonneg := (scalarRow13124.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D30.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13124])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13124