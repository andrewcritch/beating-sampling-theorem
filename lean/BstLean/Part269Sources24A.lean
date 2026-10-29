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
import BstLean.Part269Direction24
import BstLean.Part269Shared24
import BstLean.Part269Finite
import BstLean.Part269Rows24
import BstLean.Part269Source
/-! Actual 12950 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12950 ≤ (1.035458862322 : ℝ) := by
  have hr : (113.798066767410 : ℝ) ≤ √(12950 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.798066767410 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12950 12950 (11 / 1000) ≤
    (0.008399852347 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12950) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.798066767410 : ℝ) ≤ √(12950 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12950)
  have hdiv : K / √(12950 : ℝ) ≤ K / 113.798066767410 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.798066767410 ≤ (0.008399852347 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12950.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12950 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12950 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12950 := gPlus_lower 12950
end BstLean.Part269.N12950

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12950
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035458862321 : ℝ) ≤ wn 12950 := by
  have hn : √(12950 : ℝ) ≤ 113.798066767411 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12950 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.798066767411 ≤ 2 / √(12950 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246934751 : ℝ) ≤ rhoBar 12950 BstLean.Part154.csC ∧
    rhoBar 12950 BstLean.Part154.csC ≤ 0.000246935133 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035458862321 : ℝ) / (1.295212 * 12950) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035458862322 : ℝ) / (1.29521 * 12950) := by gcongr
      _ ≤ (0.000246935133 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12950 BstLean.Part154.csC) ≤ 0.000987801509 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12950 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) ≤ 0.000188610548 ∧
    cc1 (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) ≤ 0.000120014180 ∧
    cc2 (rhoBar 12950 BstLean.Part154.csC) ≤ 0.000069669194 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12950 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12950 BstLean.Part154.csC * nuR (rhoBar 12950 BstLean.Part154.csC)) ≤ 0.000493885511 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246935133 : ℝ) * 0.000987801509 := by gcongr
      _ ≤ (0.000493885511 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12950 BstLean.Part154.csC) * nuR (rhoBar 12950 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987801509 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12950 BstLean.Part154.csC) * rhoBar 12950 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246935133 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246935133 / 2 + 0.399 * 0.000987801509 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188610548 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493885511 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120014180 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246935133 / 1.414213562 := by gcongr
      _ ≤ (0.000069669194 : ℝ) := by norm_num

end BstLean.Part269.N12950

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12950
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) ≤ 1.53627E-7 := by
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12950 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12950 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188610548 : ℝ) ^ 2 + 0.000120014180 ^ 2 + 3 * 0.000069669194 ^ 2 +
        2 * 0.797885 * 0.000188610548 * 0.000120014180 + 2 * 0.000188610548 * 0.000069669194 +
        4 * 0.797885 * 0.000120014180 * 0.000069669194 := by gcongr
    _ ≤ (1.53627E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12950 BstLean.Part154.csC Θ ≤ 0.002576784969 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12950 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12950 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035458862322 * 1.53627E-7 / (0.000246934751 : ℝ) := by gcongr
    _ ≤ 0.002576784969 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12950 BstLean.Part154.csC Θ ≤ 0.002858113000 + 0.000651112359 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12950 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035458862322 : ℝ) * ((2 * Θ * 0.000246935133 +
        (6863 / 10000) * 0.000246935133 * 12950 * 0.000987801509) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002858113000 + 0.000651112359 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12950 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12950 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12950 0.011 Θ ∧ gammaRatio 12950 0.011 Θ ≤ 0.000084889914 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12950 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035458862322 : ℝ) * 0.525 / ((1 - 0.011) * 12950) := by gcongr
      _ ≤ (0.000084889914 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12950 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12950 0.011 Θ) :=
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
    badAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12950 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12950 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12950 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12950 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12950 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12950 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12950 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12950 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12950 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12950 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035458862322 : ℝ) * 12950 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279469477 + 0.003227897328 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12950

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12950
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12950 BstLean.Part154.csC) (piBar (rhoBar 12950 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12950 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12950 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12950 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12950 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12950 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12950 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12950 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12950 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12950 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051969771981 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12950) ≤ 0.010494357374 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12950 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035458862322)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010494357374 + 2 * 0.737676 / 12950) := by gcongr
    _ ≤ (0.051969771981 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12950 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12950

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12950
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514655776 : ℝ) ≤ plow 12950 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12950) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480715575)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352812109) : eMP 12950 0.011 xi bn ≤ 0.001164974416 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12950 : ℝ) * (1 - 0.011))) ≤ 0.000576050651 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352812109 / (12950 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576050651 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576050651 : ℝ) + 3.141593 * 0.052480715575 / (12950 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164974416 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480715575)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352812109) : PiBarMP 12950 12 0.011 xi bn ≤ 0.159671296432 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12950 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036780594191 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.170446672265 : ℝ) ≤ √((12950 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.798066767410 : ℝ) ≤ √(12950 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12950) ≤ 0.122430974959 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036780594191 + 0.052480715575 * 1.772454 / (2 * (113.170446672265 : ℝ))) * (1 + 0.001164974416) +
        8 / (12950 * 113.798066767410) + 0.122430974959 := by gcongr
    _ ≤ (0.159671296432 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480715575)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352812109) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281056470799) :
    parallelOracle 12950 0.011 xi bn cd ≤ 0.160642280602 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12950 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12950 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514655776 : ℝ) ≤ plow 12950 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.798066767410 : ℝ) ≤ √(12950 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281056470799 : ℝ) / (2 * 0.560514655776 * 113.798066767410)) * 0.159671296432 +
        0.281056470799 ^ 2 / (2 * 0.560514655776 * 113.798066767410) := by gcongr
    _ ≤ (0.160642280602 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480715575) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352812109)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281056470799) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12950 12950 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514655776 : ℝ) ≤ plow 12950 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.798066767410 : ℝ) ≤ √(12950 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12950 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12950 Θ 1.22 ≤ 0.011653102181 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.798066767410 := by gcongr <;> linarith
      _ ≤ (0.011653102181 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12950 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12950 12950 0.011 ≤ 0.008399852347 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12950 12950 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12950 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12950 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12950 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12950 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160642280602 + 0.011653102181 + (0.008399852347 : ℝ) *
        (1 + 2 * (0.281056470799 + 0.011653102181) / (0.560514655776 * 113.798066767410))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12950]

end BstLean.Part269.N12950

/-! The original eight local profiles supply actual 12950 moment certificates. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12950 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052480715575 ∧
    0 ≤ bN 12950 BstLean.Part154.csC (groupTheta g) ∧ bN 12950 BstLean.Part154.csC (groupTheta g) ≤ 0.001352812109 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12950 12950 0.011
      (momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12950 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12950 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12950 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229086698818 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12950 0.011
      (momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12950 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12950
/-! The actual computed-centre upper energy formula at 12950. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12950

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12950)
open BstLean.Part268 (cell12950)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084792412563
  | 2 => 0.085723019123
  | 3 => 0.086650105699
  | 4 => 0.087574700712
  | 5 => 0.088498059712
  | 6 => 0.089421700563
  | 7 => 0.090347442223
  | 8 => 0.091277447192
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12950 12950 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12950 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12950

/-! Actual upper energy certificates on all 43 source endpoints at 12950. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12950)
open BstLean.Part268 (cell12950)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12950 (gMinus 12950) (1 - (cell12950 i).lower) ≤ 1 ∧
    energyUpper 12950 (gMinus 12950) (BstLean.Part211.gPlus 12950)
      (finiteEnergy 12950 12950 0.011) (1 - (cell12950 i).lower) ≤
      (cell12950 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨10,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨11,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨12,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨13,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨14,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨15,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨16,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨17,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨18,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨19,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨20,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨21,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨22,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨23,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨24,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨25,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨26,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨27,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨28,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨29,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨30,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨31,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨32,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨33,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨34,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨35,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨36,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨37,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨38,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨39,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨40,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨41,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨42,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨43,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨44,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨45,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨46,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨47,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨48,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨49,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨50,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨51,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12950) (by norm_num)
        (q := 1 - (cell12950 ⟨52,by decide⟩).lower)
        (by norm_num [cell12950]) (by norm_num [cell12950])
      exact ⟨E.1,E.2.trans (by norm_num [cell12950])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12950

/-! Source-cell containment and simple scalar guards at 12950. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12950)
open BstLean.Part268 (cell12950)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12950 ⟨10,by decide⟩).lower ∧ (cell12950 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12950 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12950 ⟨11,by decide⟩).lower ∧ (cell12950 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12950 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12950 ⟨12,by decide⟩).lower ∧ (cell12950 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12950 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12950 ⟨13,by decide⟩).lower ∧ (cell12950 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12950 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12950 ⟨14,by decide⟩).lower ∧ (cell12950 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12950 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12950 ⟨15,by decide⟩).lower ∧ (cell12950 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12950 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12950 ⟨16,by decide⟩).lower ∧ (cell12950 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12950 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12950 ⟨17,by decide⟩).lower ∧ (cell12950 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12950 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12950 ⟨18,by decide⟩).lower ∧ (cell12950 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12950 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12950 ⟨19,by decide⟩).lower ∧ (cell12950 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12950 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12950 ⟨20,by decide⟩).lower ∧ (cell12950 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12950 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12950 ⟨21,by decide⟩).lower ∧ (cell12950 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12950 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12950 ⟨22,by decide⟩).lower ∧ (cell12950 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12950 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12950 ⟨23,by decide⟩).lower ∧ (cell12950 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12950 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12950 ⟨24,by decide⟩).lower ∧ (cell12950 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12950 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12950 ⟨25,by decide⟩).lower ∧ (cell12950 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12950 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12950 ⟨26,by decide⟩).lower ∧ (cell12950 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12950 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12950 ⟨27,by decide⟩).lower ∧ (cell12950 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12950 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12950 ⟨28,by decide⟩).lower ∧ (cell12950 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12950 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12950 ⟨29,by decide⟩).lower ∧ (cell12950 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12950 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12950 ⟨30,by decide⟩).lower ∧ (cell12950 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12950 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12950 ⟨31,by decide⟩).lower ∧ (cell12950 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12950 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12950 ⟨32,by decide⟩).lower ∧ (cell12950 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12950 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12950 ⟨33,by decide⟩).lower ∧ (cell12950 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12950 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12950 ⟨34,by decide⟩).lower ∧ (cell12950 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12950 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12950 ⟨35,by decide⟩).lower ∧ (cell12950 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12950 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12950 ⟨36,by decide⟩).lower ∧ (cell12950 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12950 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12950 ⟨37,by decide⟩).lower ∧ (cell12950 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12950 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12950 ⟨38,by decide⟩).lower ∧ (cell12950 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12950 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12950 ⟨39,by decide⟩).lower ∧ (cell12950 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12950 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12950 ⟨40,by decide⟩).lower ∧ (cell12950 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12950 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12950 ⟨41,by decide⟩).lower ∧ (cell12950 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12950 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12950 ⟨42,by decide⟩).lower ∧ (cell12950 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12950 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12950 ⟨43,by decide⟩).lower ∧ (cell12950 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12950 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12950 ⟨44,by decide⟩).lower ∧ (cell12950 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12950 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12950 ⟨45,by decide⟩).lower ∧ (cell12950 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12950 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12950 ⟨46,by decide⟩).lower ∧ (cell12950 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12950 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12950 ⟨47,by decide⟩).lower ∧ (cell12950 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12950 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12950 ⟨48,by decide⟩).lower ∧ (cell12950 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12950 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12950 ⟨49,by decide⟩).lower ∧ (cell12950 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12950 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12950 ⟨50,by decide⟩).lower ∧ (cell12950 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12950 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12950 ⟨51,by decide⟩).lower ∧ (cell12950 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12950 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12950 ⟨52,by decide⟩).lower ∧ (cell12950 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12950 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12950 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12950 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12950,cell12950,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12950 i).lower ∧
    (cell12950 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12950 i).upper ≤ (0.532 : ℝ) ∧
    (cell12950 i).centre ≤ (0.1 : ℝ) ∧ (cell12950 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12950 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12950 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12950

/-! The local source numeric instances at 12950 have no network premises. -/
namespace BstLean.Part269.N12950
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12950)
open BstLean.Part268 (cell12950)

noncomputable def sourceNumerics12950 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12950 (cell12950 i)
      scalarRow12950.M scalarRow12950.H scalarRow12950.xi := by
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
    energy_allowance := scalarRow12950.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12950]
    centre_nonneg := (scalarRow12950.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12950])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12950
/-! Actual 12951 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12951 ≤ (1.035457481409 : ℝ) := by
  have hr : (113.802460430343 : ℝ) ≤ √(12951 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.802460430343 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12951 12951 (11 / 1000) ≤
    (0.008399528044 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12951) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.802460430343 : ℝ) ≤ √(12951 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12951)
  have hdiv : K / √(12951 : ℝ) ≤ K / 113.802460430343 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.802460430343 ≤ (0.008399528044 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12951.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12951 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12951 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12951 := gPlus_lower 12951
end BstLean.Part269.N12951

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12951
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035457481408 : ℝ) ≤ wn 12951 := by
  have hn : √(12951 : ℝ) ≤ 113.802460430344 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12951 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.802460430344 ≤ 2 / √(12951 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246915355 : ℝ) ≤ rhoBar 12951 BstLean.Part154.csC ∧
    rhoBar 12951 BstLean.Part154.csC ≤ 0.000246915737 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035457481408 : ℝ) / (1.295212 * 12951) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035457481409 : ℝ) / (1.29521 * 12951) := by gcongr
      _ ≤ (0.000246915737 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12951 BstLean.Part154.csC) ≤ 0.000987723916 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12951 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) ≤ 0.000188595733 ∧
    cc1 (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) ≤ 0.000120004752 ∧
    cc2 (rhoBar 12951 BstLean.Part154.csC) ≤ 0.000069663722 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12951 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12951 BstLean.Part154.csC * nuR (rhoBar 12951 BstLean.Part154.csC)) ≤ 0.000493846716 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246915737 : ℝ) * 0.000987723916 := by gcongr
      _ ≤ (0.000493846716 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12951 BstLean.Part154.csC) * nuR (rhoBar 12951 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987723916 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12951 BstLean.Part154.csC) * rhoBar 12951 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246915737 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246915737 / 2 + 0.399 * 0.000987723916 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188595733 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493846716 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120004752 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246915737 / 1.414213562 := by gcongr
      _ ≤ (0.000069663722 : ℝ) := by norm_num

end BstLean.Part269.N12951

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12951
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) ≤ 1.53603E-7 := by
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12951 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12951 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188595733 : ℝ) ^ 2 + 0.000120004752 ^ 2 + 3 * 0.000069663722 ^ 2 +
        2 * 0.797885 * 0.000188595733 * 0.000120004752 + 2 * 0.000188595733 * 0.000069663722 +
        4 * 0.797885 * 0.000120004752 * 0.000069663722 := by gcongr
    _ ≤ (1.53603E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12951 BstLean.Part154.csC Θ ≤ 0.002576581364 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12951 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12951 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035457481409 * 1.53603E-7 / (0.000246915355 : ℝ) := by gcongr
    _ ≤ 0.002576581364 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12951 BstLean.Part154.csC Θ ≤ 0.002857880871 + 0.000651060347 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12951 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035457481409 : ℝ) * ((2 * Θ * 0.000246915737 +
        (6863 / 10000) * 0.000246915737 * 12951 * 0.000987723916) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002857880871 + 0.000651060347 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12951 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12951 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12951 0.011 Θ ∧ gammaRatio 12951 0.011 Θ ≤ 0.000084883246 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12951 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035457481409 : ℝ) * 0.525 / ((1 - 0.011) * 12951) := by gcongr
      _ ≤ (0.000084883246 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12951 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12951 0.011 Θ) :=
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
    badAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12951 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12951 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12951 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12951 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12951 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12951 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12951 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12951 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12951 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12951 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035457481409 : ℝ) * 12951 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279237348 + 0.003227641711 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12951

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12951
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12951 BstLean.Part154.csC) (piBar (rhoBar 12951 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12951 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12951 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12951 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12951 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12951 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12951 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12951 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12951 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12951 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051967743995 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12951) ≤ 0.010493952210 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12951 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035457481409)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010493952210 + 2 * 0.737676 / 12951) := by gcongr
    _ ≤ (0.051967743995 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12951 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12951

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12951
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514699266 : ℝ) ≤ plow 12951 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12951) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480349247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352705217) : eMP 12951 0.011 xi bn ≤ 0.001164883336 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12951 : ℝ) * (1 - 0.011))) ≤ 0.000576005653 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352705217 / (12951 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576005653 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576005653 : ℝ) + 3.141593 * 0.052480349247 / (12951 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164883336 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480349247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352705217) : PiBarMP 12951 12 0.011 xi bn ≤ 0.159665092043 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12951 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036779141059 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.174816103230 : ℝ) ≤ √((12951 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.802460430343 : ℝ) ≤ √(12951 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12951) ≤ 0.122426248168 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036779141059 + 0.052480349247 * 1.772454 / (2 * (113.174816103230 : ℝ))) * (1 + 0.001164883336) +
        8 / (12951 * 113.802460430343) + 0.122426248168 := by gcongr
    _ ≤ (0.159665092043 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480349247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352705217) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281053643271) :
    parallelOracle 12951 0.011 xi bn cd ≤ 0.160636008984 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12951 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12951 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514699266 : ℝ) ≤ plow 12951 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.802460430343 : ℝ) ≤ √(12951 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281053643271 : ℝ) / (2 * 0.560514699266 * 113.802460430343)) * 0.159665092043 +
        0.281053643271 ^ 2 / (2 * 0.560514699266 * 113.802460430343) := by gcongr
    _ ≤ (0.160636008984 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052480349247) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352705217)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281053643271) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12951 12951 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514699266 : ℝ) ≤ plow 12951 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.802460430343 : ℝ) ≤ √(12951 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12951 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12951 Θ 1.22 ≤ 0.011652652280 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.802460430343 := by gcongr <;> linarith
      _ ≤ (0.011652652280 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12951 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12951 12951 0.011 ≤ 0.008399528044 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12951 12951 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12951 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12951 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12951 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12951 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160636008984 + 0.011652652280 + (0.008399528044 : ℝ) *
        (1 + 2 * (0.281053643271 + 0.011652652280) / (0.560514699266 * 113.802460430343))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12951]

end BstLean.Part269.N12951

/-! The original eight local profiles supply actual 12951 moment certificates. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12951 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052480349247 ∧
    0 ≤ bN 12951 BstLean.Part154.csC (groupTheta g) ∧ bN 12951 BstLean.Part154.csC (groupTheta g) ≤ 0.001352705217 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12951 12951 0.011
      (momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12951 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12951 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12951 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229085899276 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12951 0.011
      (momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12951 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12951
/-! The actual computed-centre upper energy formula at 12951. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12951

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12951)
open BstLean.Part268 (cell12951)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084789736769
  | 2 => 0.085720299272
  | 3 => 0.086647336216
  | 4 => 0.087571874683
  | 5 => 0.088495168638
  | 6 => 0.089418734087
  | 7 => 0.090344387814
  | 8 => 0.091274289798
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12951 12951 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12951 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12951

/-! Actual upper energy certificates on all 43 source endpoints at 12951. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12951)
open BstLean.Part268 (cell12951)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12951 (gMinus 12951) (1 - (cell12951 i).lower) ≤ 1 ∧
    energyUpper 12951 (gMinus 12951) (BstLean.Part211.gPlus 12951)
      (finiteEnergy 12951 12951 0.011) (1 - (cell12951 i).lower) ≤
      (cell12951 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨10,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨11,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨12,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨13,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨14,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨15,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨16,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨17,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨18,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨19,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨20,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨21,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨22,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨23,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨24,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨25,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨26,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨27,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨28,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨29,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨30,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨31,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨32,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨33,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨34,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨35,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨36,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨37,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨38,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨39,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨40,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨41,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨42,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨43,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨44,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨45,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨46,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨47,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨48,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨49,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨50,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨51,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12951) (by norm_num)
        (q := 1 - (cell12951 ⟨52,by decide⟩).lower)
        (by norm_num [cell12951]) (by norm_num [cell12951])
      exact ⟨E.1,E.2.trans (by norm_num [cell12951])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12951

/-! Source-cell containment and simple scalar guards at 12951. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12951)
open BstLean.Part268 (cell12951)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12951 ⟨10,by decide⟩).lower ∧ (cell12951 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12951 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12951 ⟨11,by decide⟩).lower ∧ (cell12951 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12951 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12951 ⟨12,by decide⟩).lower ∧ (cell12951 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12951 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12951 ⟨13,by decide⟩).lower ∧ (cell12951 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12951 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12951 ⟨14,by decide⟩).lower ∧ (cell12951 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12951 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12951 ⟨15,by decide⟩).lower ∧ (cell12951 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12951 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12951 ⟨16,by decide⟩).lower ∧ (cell12951 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12951 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12951 ⟨17,by decide⟩).lower ∧ (cell12951 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12951 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12951 ⟨18,by decide⟩).lower ∧ (cell12951 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12951 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12951 ⟨19,by decide⟩).lower ∧ (cell12951 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12951 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12951 ⟨20,by decide⟩).lower ∧ (cell12951 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12951 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12951 ⟨21,by decide⟩).lower ∧ (cell12951 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12951 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12951 ⟨22,by decide⟩).lower ∧ (cell12951 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12951 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12951 ⟨23,by decide⟩).lower ∧ (cell12951 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12951 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12951 ⟨24,by decide⟩).lower ∧ (cell12951 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12951 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12951 ⟨25,by decide⟩).lower ∧ (cell12951 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12951 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12951 ⟨26,by decide⟩).lower ∧ (cell12951 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12951 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12951 ⟨27,by decide⟩).lower ∧ (cell12951 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12951 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12951 ⟨28,by decide⟩).lower ∧ (cell12951 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12951 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12951 ⟨29,by decide⟩).lower ∧ (cell12951 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12951 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12951 ⟨30,by decide⟩).lower ∧ (cell12951 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12951 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12951 ⟨31,by decide⟩).lower ∧ (cell12951 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12951 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12951 ⟨32,by decide⟩).lower ∧ (cell12951 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12951 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12951 ⟨33,by decide⟩).lower ∧ (cell12951 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12951 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12951 ⟨34,by decide⟩).lower ∧ (cell12951 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12951 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12951 ⟨35,by decide⟩).lower ∧ (cell12951 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12951 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12951 ⟨36,by decide⟩).lower ∧ (cell12951 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12951 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12951 ⟨37,by decide⟩).lower ∧ (cell12951 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12951 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12951 ⟨38,by decide⟩).lower ∧ (cell12951 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12951 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12951 ⟨39,by decide⟩).lower ∧ (cell12951 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12951 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12951 ⟨40,by decide⟩).lower ∧ (cell12951 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12951 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12951 ⟨41,by decide⟩).lower ∧ (cell12951 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12951 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12951 ⟨42,by decide⟩).lower ∧ (cell12951 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12951 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12951 ⟨43,by decide⟩).lower ∧ (cell12951 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12951 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12951 ⟨44,by decide⟩).lower ∧ (cell12951 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12951 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12951 ⟨45,by decide⟩).lower ∧ (cell12951 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12951 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12951 ⟨46,by decide⟩).lower ∧ (cell12951 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12951 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12951 ⟨47,by decide⟩).lower ∧ (cell12951 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12951 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12951 ⟨48,by decide⟩).lower ∧ (cell12951 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12951 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12951 ⟨49,by decide⟩).lower ∧ (cell12951 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12951 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12951 ⟨50,by decide⟩).lower ∧ (cell12951 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12951 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12951 ⟨51,by decide⟩).lower ∧ (cell12951 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12951 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12951 ⟨52,by decide⟩).lower ∧ (cell12951 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12951 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12951 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12951 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12951,cell12951,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12951 i).lower ∧
    (cell12951 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12951 i).upper ≤ (0.532 : ℝ) ∧
    (cell12951 i).centre ≤ (0.1 : ℝ) ∧ (cell12951 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12951 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12951 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12951

/-! The local source numeric instances at 12951 have no network premises. -/
namespace BstLean.Part269.N12951
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12951)
open BstLean.Part268 (cell12951)

noncomputable def sourceNumerics12951 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12951 (cell12951 i)
      scalarRow12951.M scalarRow12951.H scalarRow12951.xi := by
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
    energy_allowance := scalarRow12951.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12951]
    centre_nonneg := (scalarRow12951.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12951])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12951
/-! Actual 12952 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12952 ≤ (1.035456100656 : ℝ) := by
  have hr : (113.806853923654 : ℝ) ≤ √(12952 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.806853923654 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12952 12952 (11 / 1000) ≤
    (0.008399203780 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12952) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.806853923654 : ℝ) ≤ √(12952 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12952)
  have hdiv : K / √(12952 : ℝ) ≤ K / 113.806853923654 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.806853923654 ≤ (0.008399203780 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12952.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12952 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12952 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12952 := gPlus_lower 12952
end BstLean.Part269.N12952

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12952
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035456100655 : ℝ) ≤ wn 12952 := by
  have hn : √(12952 : ℝ) ≤ 113.806853923655 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12952 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.806853923655 ≤ 2 / √(12952 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246895962 : ℝ) ≤ rhoBar 12952 BstLean.Part154.csC ∧
    rhoBar 12952 BstLean.Part154.csC ≤ 0.000246896344 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035456100655 : ℝ) / (1.295212 * 12952) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035456100656 : ℝ) / (1.29521 * 12952) := by gcongr
      _ ≤ (0.000246896344 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12952 BstLean.Part154.csC) ≤ 0.000987646334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12952 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) ≤ 0.000188580919 ∧
    cc1 (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) ≤ 0.000119995327 ∧
    cc2 (rhoBar 12952 BstLean.Part154.csC) ≤ 0.000069658250 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12952 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12952 BstLean.Part154.csC * nuR (rhoBar 12952 BstLean.Part154.csC)) ≤ 0.000493807928 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246896344 : ℝ) * 0.000987646334 := by gcongr
      _ ≤ (0.000493807928 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12952 BstLean.Part154.csC) * nuR (rhoBar 12952 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987646334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12952 BstLean.Part154.csC) * rhoBar 12952 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246896344 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246896344 / 2 + 0.399 * 0.000987646334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188580919 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493807928 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119995327 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246896344 / 1.414213562 := by gcongr
      _ ≤ (0.000069658250 : ℝ) := by norm_num

end BstLean.Part269.N12952

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12952
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) ≤ 1.53579E-7 := by
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12952 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12952 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188580919 : ℝ) ^ 2 + 0.000119995327 ^ 2 + 3 * 0.000069658250 ^ 2 +
        2 * 0.797885 * 0.000188580919 * 0.000119995327 + 2 * 0.000188580919 * 0.000069658250 +
        4 * 0.797885 * 0.000119995327 * 0.000069658250 := by gcongr
    _ ≤ (1.53579E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12952 BstLean.Part154.csC Θ ≤ 0.002576377697 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12952 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12952 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035456100656 * 1.53579E-7 / (0.000246895962 : ℝ) := by gcongr
    _ ≤ 0.002576377697 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12952 BstLean.Part154.csC Θ ≤ 0.002857648775 + 0.000651008344 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12952 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035456100656 : ℝ) * ((2 * Θ * 0.000246896344 +
        (6863 / 10000) * 0.000246896344 * 12952 * 0.000987646334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002857648775 + 0.000651008344 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12952 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12952 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12952 0.011 Θ ∧ gammaRatio 12952 0.011 Θ ≤ 0.000084876579 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12952 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035456100656 : ℝ) * 0.525 / ((1 - 0.011) * 12952) := by gcongr
      _ ≤ (0.000084876579 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12952 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12952 0.011 Θ) :=
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
    badAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12952 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12952 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12952 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12952 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12952 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12952 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12952 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12952 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12952 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12952 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035456100656 : ℝ) * 12952 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003279005252 + 0.003227386041 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12952

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12952
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12952 BstLean.Part154.csC) (piBar (rhoBar 12952 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12952 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12952 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12952 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12952 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12952 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12952 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12952 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12952 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12952 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051965716247 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12952) ≤ 0.010493547093 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12952 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035456100656)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010493547093 + 2 * 0.737676 / 12952) := by gcongr
    _ ≤ (0.051965716247 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12952 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12952

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12952
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514742750 : ℝ) ≤ plow 12952 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12952) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479982924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352598291) : eMP 12952 0.011 xi bn ≤ 0.001164792249 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12952 : ℝ) * (1 - 0.011))) ≤ 0.000575960651 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352598291 / (12952 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575960651 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575960651 : ℝ) + 3.141593 * 0.052479982924 / (12952 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164792249 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479982924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352598291) : PiBarMP 12952 12 0.011 xi bn ≤ 0.159658887684 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12952 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036777687407 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.179185365507 : ℝ) ≤ √((12952 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.806853923654 : ℝ) ≤ √(12952 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12952) ≤ 0.122421521925 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036777687407 + 0.052479982924 * 1.772454 / (2 * (113.179185365507 : ℝ))) * (1 + 0.001164792249) +
        8 / (12952 * 113.806853923654) + 0.122421521925 := by gcongr
    _ ≤ (0.159658887684 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479982924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352598291) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281050815990) :
    parallelOracle 12952 0.011 xi bn cd ≤ 0.160629737405 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12952 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12952 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514742750 : ℝ) ≤ plow 12952 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.806853923654 : ℝ) ≤ √(12952 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281050815990 : ℝ) / (2 * 0.560514742750 * 113.806853923654)) * 0.159658887684 +
        0.281050815990 ^ 2 / (2 * 0.560514742750 * 113.806853923654) := by gcongr
    _ ≤ (0.160629737405 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479982924) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352598291)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281050815990) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12952 12952 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514742750 : ℝ) ≤ plow 12952 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.806853923654 : ℝ) ≤ √(12952 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12952 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12952 Θ 1.22 ≤ 0.011652202432 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.806853923654 := by gcongr <;> linarith
      _ ≤ (0.011652202432 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12952 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12952 12952 0.011 ≤ 0.008399203780 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12952 12952 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12952 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12952 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12952 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12952 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160629737405 + 0.011652202432 + (0.008399203780 : ℝ) *
        (1 + 2 * (0.281050815990 + 0.011652202432) / (0.560514742750 * 113.806853923654))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12952]

end BstLean.Part269.N12952

/-! The original eight local profiles supply actual 12952 moment certificates. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12952 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052479982924 ∧
    0 ≤ bN 12952 BstLean.Part154.csC (groupTheta g) ∧ bN 12952 BstLean.Part154.csC (groupTheta g) ≤ 0.001352598291 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12952 12952 0.011
      (momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12952 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12952 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12952 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229085099743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12952 0.011
      (momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12952 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12952
/-! The actual computed-centre upper energy formula at 12952. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12952

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12952)
open BstLean.Part268 (cell12952)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084787061822
  | 2 => 0.085717580303
  | 3 => 0.086644567654
  | 4 => 0.087569049622
  | 5 => 0.088492278593
  | 6 => 0.089415768713
  | 7 => 0.090341334596
  | 8 => 0.091271133703
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12952 12952 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12952 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12952

/-! Actual upper energy certificates on all 43 source endpoints at 12952. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12952)
open BstLean.Part268 (cell12952)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12952 (gMinus 12952) (1 - (cell12952 i).lower) ≤ 1 ∧
    energyUpper 12952 (gMinus 12952) (BstLean.Part211.gPlus 12952)
      (finiteEnergy 12952 12952 0.011) (1 - (cell12952 i).lower) ≤
      (cell12952 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨10,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨11,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨12,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨13,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨14,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨15,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨16,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨17,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨18,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨19,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨20,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨21,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨22,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨23,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨24,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨25,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨26,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨27,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨28,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨29,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨30,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨31,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨32,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨33,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨34,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨35,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨36,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨37,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨38,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨39,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨40,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨41,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨42,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨43,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨44,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨45,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨46,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨47,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨48,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨49,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨50,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨51,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12952) (by norm_num)
        (q := 1 - (cell12952 ⟨52,by decide⟩).lower)
        (by norm_num [cell12952]) (by norm_num [cell12952])
      exact ⟨E.1,E.2.trans (by norm_num [cell12952])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12952

/-! Source-cell containment and simple scalar guards at 12952. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12952)
open BstLean.Part268 (cell12952)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12952 ⟨10,by decide⟩).lower ∧ (cell12952 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12952 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12952 ⟨11,by decide⟩).lower ∧ (cell12952 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12952 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12952 ⟨12,by decide⟩).lower ∧ (cell12952 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12952 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12952 ⟨13,by decide⟩).lower ∧ (cell12952 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12952 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12952 ⟨14,by decide⟩).lower ∧ (cell12952 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12952 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12952 ⟨15,by decide⟩).lower ∧ (cell12952 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12952 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12952 ⟨16,by decide⟩).lower ∧ (cell12952 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12952 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12952 ⟨17,by decide⟩).lower ∧ (cell12952 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12952 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12952 ⟨18,by decide⟩).lower ∧ (cell12952 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12952 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12952 ⟨19,by decide⟩).lower ∧ (cell12952 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12952 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12952 ⟨20,by decide⟩).lower ∧ (cell12952 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12952 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12952 ⟨21,by decide⟩).lower ∧ (cell12952 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12952 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12952 ⟨22,by decide⟩).lower ∧ (cell12952 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12952 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12952 ⟨23,by decide⟩).lower ∧ (cell12952 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12952 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12952 ⟨24,by decide⟩).lower ∧ (cell12952 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12952 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12952 ⟨25,by decide⟩).lower ∧ (cell12952 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12952 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12952 ⟨26,by decide⟩).lower ∧ (cell12952 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12952 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12952 ⟨27,by decide⟩).lower ∧ (cell12952 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12952 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12952 ⟨28,by decide⟩).lower ∧ (cell12952 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12952 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12952 ⟨29,by decide⟩).lower ∧ (cell12952 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12952 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12952 ⟨30,by decide⟩).lower ∧ (cell12952 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12952 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12952 ⟨31,by decide⟩).lower ∧ (cell12952 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12952 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12952 ⟨32,by decide⟩).lower ∧ (cell12952 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12952 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12952 ⟨33,by decide⟩).lower ∧ (cell12952 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12952 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12952 ⟨34,by decide⟩).lower ∧ (cell12952 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12952 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12952 ⟨35,by decide⟩).lower ∧ (cell12952 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12952 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12952 ⟨36,by decide⟩).lower ∧ (cell12952 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12952 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12952 ⟨37,by decide⟩).lower ∧ (cell12952 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12952 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12952 ⟨38,by decide⟩).lower ∧ (cell12952 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12952 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12952 ⟨39,by decide⟩).lower ∧ (cell12952 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12952 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12952 ⟨40,by decide⟩).lower ∧ (cell12952 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12952 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12952 ⟨41,by decide⟩).lower ∧ (cell12952 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12952 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12952 ⟨42,by decide⟩).lower ∧ (cell12952 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12952 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12952 ⟨43,by decide⟩).lower ∧ (cell12952 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12952 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12952 ⟨44,by decide⟩).lower ∧ (cell12952 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12952 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12952 ⟨45,by decide⟩).lower ∧ (cell12952 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12952 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12952 ⟨46,by decide⟩).lower ∧ (cell12952 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12952 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12952 ⟨47,by decide⟩).lower ∧ (cell12952 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12952 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12952 ⟨48,by decide⟩).lower ∧ (cell12952 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12952 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12952 ⟨49,by decide⟩).lower ∧ (cell12952 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12952 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12952 ⟨50,by decide⟩).lower ∧ (cell12952 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12952 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12952 ⟨51,by decide⟩).lower ∧ (cell12952 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12952 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12952 ⟨52,by decide⟩).lower ∧ (cell12952 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12952 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12952 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12952 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12952,cell12952,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12952 i).lower ∧
    (cell12952 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12952 i).upper ≤ (0.532 : ℝ) ∧
    (cell12952 i).centre ≤ (0.1 : ℝ) ∧ (cell12952 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12952 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12952 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12952

/-! The local source numeric instances at 12952 have no network premises. -/
namespace BstLean.Part269.N12952
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12952)
open BstLean.Part268 (cell12952)

noncomputable def sourceNumerics12952 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12952 (cell12952 i)
      scalarRow12952.M scalarRow12952.H scalarRow12952.xi := by
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
    energy_allowance := scalarRow12952.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12952]
    centre_nonneg := (scalarRow12952.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12952])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12952
/-! Actual 12953 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12953 ≤ (1.035454720065 : ℝ) := by
  have hr : (113.811247247361 : ℝ) ≤ √(12953 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.811247247361 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12953 12953 (11 / 1000) ≤
    (0.008398879552 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12953) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.811247247361 : ℝ) ≤ √(12953 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12953)
  have hdiv : K / √(12953 : ℝ) ≤ K / 113.811247247361 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.811247247361 ≤ (0.008398879552 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12953.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12953 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12953 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12953 := gPlus_lower 12953
end BstLean.Part269.N12953

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12953
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035454720064 : ℝ) ≤ wn 12953 := by
  have hn : √(12953 : ℝ) ≤ 113.811247247362 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12953 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.811247247362 ≤ 2 / √(12953 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246876572 : ℝ) ≤ rhoBar 12953 BstLean.Part154.csC ∧
    rhoBar 12953 BstLean.Part154.csC ≤ 0.000246876954 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035454720064 : ℝ) / (1.295212 * 12953) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035454720065 : ℝ) / (1.29521 * 12953) := by gcongr
      _ ≤ (0.000246876954 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12953 BstLean.Part154.csC) ≤ 0.000987568765 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12953 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) ≤ 0.000188566109 ∧
    cc1 (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) ≤ 0.000119985903 ∧
    cc2 (rhoBar 12953 BstLean.Part154.csC) ≤ 0.000069652779 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12953 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12953 BstLean.Part154.csC * nuR (rhoBar 12953 BstLean.Part154.csC)) ≤ 0.000493769146 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246876954 : ℝ) * 0.000987568765 := by gcongr
      _ ≤ (0.000493769146 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12953 BstLean.Part154.csC) * nuR (rhoBar 12953 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987568765 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12953 BstLean.Part154.csC) * rhoBar 12953 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246876954 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246876954 / 2 + 0.399 * 0.000987568765 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188566109 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493769146 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119985903 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246876954 / 1.414213562 := by gcongr
      _ ≤ (0.000069652779 : ℝ) := by norm_num

end BstLean.Part269.N12953

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12953
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) ≤ 1.53555E-7 := by
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12953 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12953 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188566109 : ℝ) ^ 2 + 0.000119985903 ^ 2 + 3 * 0.000069652779 ^ 2 +
        2 * 0.797885 * 0.000188566109 * 0.000119985903 + 2 * 0.000188566109 * 0.000069652779 +
        4 * 0.797885 * 0.000119985903 * 0.000069652779 := by gcongr
    _ ≤ (1.53555E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12953 BstLean.Part154.csC Θ ≤ 0.002576173969 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12953 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12953 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035454720065 * 1.53555E-7 / (0.000246876572 : ℝ) := by gcongr
    _ ≤ 0.002576173969 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12953 BstLean.Part154.csC Θ ≤ 0.002857416719 + 0.000650956349 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12953 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035454720065 : ℝ) * ((2 * Θ * 0.000246876954 +
        (6863 / 10000) * 0.000246876954 * 12953 * 0.000987568765) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002857416719 + 0.000650956349 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12953 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12953 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12953 0.011 Θ ∧ gammaRatio 12953 0.011 Θ ≤ 0.000084869913 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12953 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035454720065 : ℝ) * 0.525 / ((1 - 0.011) * 12953) := by gcongr
      _ ≤ (0.000084869913 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12953 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12953 0.011 Θ) :=
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
    badAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12953 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12953 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12953 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12953 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12953 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12953 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12953 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12953 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12953 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12953 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035454720065 : ℝ) * 12953 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003278773196 + 0.003227130318 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12953

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12953
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12953 BstLean.Part154.csC) (piBar (rhoBar 12953 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12953 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12953 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12953 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12953 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12953 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12953 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12953 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12953 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12953 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051963688730 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12953) ≤ 0.010493142022 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12953 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035454720065)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010493142022 + 2 * 0.737676 / 12953) := by gcongr
    _ ≤ (0.051963688730 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12953 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12953

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12953
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514786227 : ℝ) ≤ plow 12953 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12953) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479616613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352491334) : eMP 12953 0.011 xi bn ≤ 0.001164701157 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12953 : ℝ) * (1 - 0.011))) ≤ 0.000575915647 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352491334 / (12953 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575915647 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575915647 : ℝ) + 3.141593 * 0.052479616613 / (12953 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164701157 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479616613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352491334) : PiBarMP 12953 12 0.011 xi bn ≤ 0.159652683395 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12953 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036776233277 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.183554459117 : ℝ) ≤ √((12953 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.811247247361 : ℝ) ≤ √(12953 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12953) ≤ 0.122416796229 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036776233277 + 0.052479616613 * 1.772454 / (2 * (113.183554459117 : ℝ))) * (1 + 0.001164701157) +
        8 / (12953 * 113.811247247361) + 0.122416796229 := by gcongr
    _ ≤ (0.159652683395 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479616613)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352491334) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281047988963) :
    parallelOracle 12953 0.011 xi bn cd ≤ 0.160623465905 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12953 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12953 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514786227 : ℝ) ≤ plow 12953 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.811247247361 : ℝ) ≤ √(12953 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281047988963 : ℝ) / (2 * 0.560514786227 * 113.811247247361)) * 0.159652683395 +
        0.281047988963 ^ 2 / (2 * 0.560514786227 * 113.811247247361) := by gcongr
    _ ≤ (0.160623465905 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479616613) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352491334)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281047988963) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12953 12953 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514786227 : ℝ) ≤ plow 12953 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.811247247361 : ℝ) ≤ √(12953 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12953 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12953 Θ 1.22 ≤ 0.011651752635 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.811247247361 := by gcongr <;> linarith
      _ ≤ (0.011651752635 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12953 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12953 12953 0.011 ≤ 0.008398879552 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12953 12953 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12953 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12953 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12953 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12953 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160623465905 + 0.011651752635 + (0.008398879552 : ℝ) *
        (1 + 2 * (0.281047988963 + 0.011651752635) / (0.560514786227 * 113.811247247361))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12953]

end BstLean.Part269.N12953

/-! The original eight local profiles supply actual 12953 moment certificates. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12953 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052479616613 ∧
    0 ≤ bN 12953 BstLean.Part154.csC (groupTheta g) ∧ bN 12953 BstLean.Part154.csC (groupTheta g) ≤ 0.001352491334 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12953 12953 0.011
      (momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12953 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12953 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12953 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229084300233 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12953 0.011
      (momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12953 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12953
/-! The actual computed-centre upper energy formula at 12953. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12953

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12953)
open BstLean.Part268 (cell12953)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084784387723
  | 2 => 0.085714862212
  | 3 => 0.086641800011
  | 4 => 0.087566225530
  | 5 => 0.088489389577
  | 6 => 0.089412804441
  | 7 => 0.090338282568
  | 8 => 0.091267978904
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12953 12953 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12953 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12953

/-! Actual upper energy certificates on all 43 source endpoints at 12953. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12953)
open BstLean.Part268 (cell12953)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12953 (gMinus 12953) (1 - (cell12953 i).lower) ≤ 1 ∧
    energyUpper 12953 (gMinus 12953) (BstLean.Part211.gPlus 12953)
      (finiteEnergy 12953 12953 0.011) (1 - (cell12953 i).lower) ≤
      (cell12953 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨10,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨11,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨12,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨13,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨14,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨15,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨16,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨17,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨18,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨19,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨20,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨21,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨22,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨23,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨24,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨25,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨26,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨27,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨28,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨29,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨30,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨31,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨32,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨33,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨34,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨35,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨36,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨37,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨38,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨39,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨40,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨41,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨42,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨43,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨44,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨45,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨46,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨47,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨48,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨49,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨50,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨51,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12953) (by norm_num)
        (q := 1 - (cell12953 ⟨52,by decide⟩).lower)
        (by norm_num [cell12953]) (by norm_num [cell12953])
      exact ⟨E.1,E.2.trans (by norm_num [cell12953])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12953

/-! Source-cell containment and simple scalar guards at 12953. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12953)
open BstLean.Part268 (cell12953)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12953 ⟨10,by decide⟩).lower ∧ (cell12953 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12953 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12953 ⟨11,by decide⟩).lower ∧ (cell12953 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12953 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12953 ⟨12,by decide⟩).lower ∧ (cell12953 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12953 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12953 ⟨13,by decide⟩).lower ∧ (cell12953 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12953 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12953 ⟨14,by decide⟩).lower ∧ (cell12953 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12953 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12953 ⟨15,by decide⟩).lower ∧ (cell12953 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12953 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12953 ⟨16,by decide⟩).lower ∧ (cell12953 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12953 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12953 ⟨17,by decide⟩).lower ∧ (cell12953 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12953 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12953 ⟨18,by decide⟩).lower ∧ (cell12953 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12953 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12953 ⟨19,by decide⟩).lower ∧ (cell12953 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12953 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12953 ⟨20,by decide⟩).lower ∧ (cell12953 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12953 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12953 ⟨21,by decide⟩).lower ∧ (cell12953 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12953 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12953 ⟨22,by decide⟩).lower ∧ (cell12953 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12953 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12953 ⟨23,by decide⟩).lower ∧ (cell12953 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12953 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12953 ⟨24,by decide⟩).lower ∧ (cell12953 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12953 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12953 ⟨25,by decide⟩).lower ∧ (cell12953 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12953 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12953 ⟨26,by decide⟩).lower ∧ (cell12953 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12953 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12953 ⟨27,by decide⟩).lower ∧ (cell12953 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12953 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12953 ⟨28,by decide⟩).lower ∧ (cell12953 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12953 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12953 ⟨29,by decide⟩).lower ∧ (cell12953 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12953 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12953 ⟨30,by decide⟩).lower ∧ (cell12953 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12953 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12953 ⟨31,by decide⟩).lower ∧ (cell12953 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12953 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12953 ⟨32,by decide⟩).lower ∧ (cell12953 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12953 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12953 ⟨33,by decide⟩).lower ∧ (cell12953 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12953 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12953 ⟨34,by decide⟩).lower ∧ (cell12953 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12953 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12953 ⟨35,by decide⟩).lower ∧ (cell12953 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12953 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12953 ⟨36,by decide⟩).lower ∧ (cell12953 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12953 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12953 ⟨37,by decide⟩).lower ∧ (cell12953 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12953 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12953 ⟨38,by decide⟩).lower ∧ (cell12953 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12953 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12953 ⟨39,by decide⟩).lower ∧ (cell12953 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12953 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12953 ⟨40,by decide⟩).lower ∧ (cell12953 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12953 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12953 ⟨41,by decide⟩).lower ∧ (cell12953 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12953 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12953 ⟨42,by decide⟩).lower ∧ (cell12953 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12953 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12953 ⟨43,by decide⟩).lower ∧ (cell12953 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12953 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12953 ⟨44,by decide⟩).lower ∧ (cell12953 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12953 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12953 ⟨45,by decide⟩).lower ∧ (cell12953 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12953 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12953 ⟨46,by decide⟩).lower ∧ (cell12953 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12953 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12953 ⟨47,by decide⟩).lower ∧ (cell12953 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12953 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12953 ⟨48,by decide⟩).lower ∧ (cell12953 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12953 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12953 ⟨49,by decide⟩).lower ∧ (cell12953 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12953 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12953 ⟨50,by decide⟩).lower ∧ (cell12953 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12953 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12953 ⟨51,by decide⟩).lower ∧ (cell12953 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12953 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12953 ⟨52,by decide⟩).lower ∧ (cell12953 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12953 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12953 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12953 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12953,cell12953,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12953 i).lower ∧
    (cell12953 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12953 i).upper ≤ (0.532 : ℝ) ∧
    (cell12953 i).centre ≤ (0.1 : ℝ) ∧ (cell12953 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12953 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12953 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12953

/-! The local source numeric instances at 12953 have no network premises. -/
namespace BstLean.Part269.N12953
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12953)
open BstLean.Part268 (cell12953)

noncomputable def sourceNumerics12953 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12953 (cell12953 i)
      scalarRow12953.M scalarRow12953.H scalarRow12953.xi := by
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
    energy_allowance := scalarRow12953.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12953]
    centre_nonneg := (scalarRow12953.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12953])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12953
/-! Actual 12954 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12954 ≤ (1.035453339634 : ℝ) := by
  have hr : (113.815640401484 : ℝ) ≤ √(12954 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.815640401484 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12954 12954 (11 / 1000) ≤
    (0.008398555363 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12954) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.815640401484 : ℝ) ≤ √(12954 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12954)
  have hdiv : K / √(12954 : ℝ) ≤ K / 113.815640401484 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.815640401484 ≤ (0.008398555363 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12954.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12954 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12954 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12954 := gPlus_lower 12954
end BstLean.Part269.N12954

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12954
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035453339633 : ℝ) ≤ wn 12954 := by
  have hn : √(12954 : ℝ) ≤ 113.815640401485 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12954 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.815640401485 ≤ 2 / √(12954 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246857185 : ℝ) ≤ rhoBar 12954 BstLean.Part154.csC ∧
    rhoBar 12954 BstLean.Part154.csC ≤ 0.000246857567 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035453339633 : ℝ) / (1.295212 * 12954) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035453339634 : ℝ) / (1.29521 * 12954) := by gcongr
      _ ≤ (0.000246857567 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12954 BstLean.Part154.csC) ≤ 0.000987491207 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12954 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) ≤ 0.000188551300 ∧
    cc1 (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) ≤ 0.000119976480 ∧
    cc2 (rhoBar 12954 BstLean.Part154.csC) ≤ 0.000069647310 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12954 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12954 BstLean.Part154.csC * nuR (rhoBar 12954 BstLean.Part154.csC)) ≤ 0.000493730369 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246857567 : ℝ) * 0.000987491207 := by gcongr
      _ ≤ (0.000493730369 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12954 BstLean.Part154.csC) * nuR (rhoBar 12954 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987491207 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12954 BstLean.Part154.csC) * rhoBar 12954 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246857567 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246857567 / 2 + 0.399 * 0.000987491207 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188551300 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493730369 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119976480 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246857567 / 1.414213562 := by gcongr
      _ ≤ (0.000069647310 : ℝ) := by norm_num

end BstLean.Part269.N12954

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12954
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) ≤ 1.53531E-7 := by
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12954 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12954 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188551300 : ℝ) ^ 2 + 0.000119976480 ^ 2 + 3 * 0.000069647310 ^ 2 +
        2 * 0.797885 * 0.000188551300 * 0.000119976480 + 2 * 0.000188551300 * 0.000069647310 +
        4 * 0.797885 * 0.000119976480 * 0.000069647310 := by gcongr
    _ ≤ (1.53531E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12954 BstLean.Part154.csC Θ ≤ 0.002575970178 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12954 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12954 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035453339634 * 1.53531E-7 / (0.000246857185 : ℝ) := by gcongr
    _ ≤ 0.002575970178 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12954 BstLean.Part154.csC Θ ≤ 0.002857184697 + 0.000650904363 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12954 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035453339634 : ℝ) * ((2 * Θ * 0.000246857567 +
        (6863 / 10000) * 0.000246857567 * 12954 * 0.000987491207) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002857184697 + 0.000650904363 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12954 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12954 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12954 0.011 Θ ∧ gammaRatio 12954 0.011 Θ ≤ 0.000084863248 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12954 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035453339634 : ℝ) * 0.525 / ((1 - 0.011) * 12954) := by gcongr
      _ ≤ (0.000084863248 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12954 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12954 0.011 Θ) :=
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
    badAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12954 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12954 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12954 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12954 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12954 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12954 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12954 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12954 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12954 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12954 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035453339634 : ℝ) * 12954 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003278541174 + 0.003226874541 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12954

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12954
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12954 BstLean.Part154.csC) (piBar (rhoBar 12954 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12954 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12954 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12954 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12954 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12954 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12954 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12954 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12954 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12954 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051961661455 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12954) ≤ 0.010492736999 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12954 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035453339634)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010492736999 + 2 * 0.737676 / 12954) := by gcongr
    _ ≤ (0.051961661455 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12954 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12954

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12954
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514829697 : ℝ) ≤ plow 12954 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12954) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479250309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352384344) : eMP 12954 0.011 xi bn ≤ 0.001164610056 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12954 : ℝ) * (1 - 0.011))) ≤ 0.000575870638 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352384344 / (12954 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575870638 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575870638 : ℝ) + 3.141593 * 0.052479250309 / (12954 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164610056 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479250309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352384344) : PiBarMP 12954 12 0.011 xi bn ≤ 0.159646479148 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12954 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036774778640 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.187923384078 : ℝ) ≤ √((12954 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.815640401484 : ℝ) ≤ √(12954 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12954) ≤ 0.122412071080 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036774778640 + 0.052479250309 * 1.772454 / (2 * (113.187923384078 : ℝ))) * (1 + 0.001164610056) +
        8 / (12954 * 113.815640401484) + 0.122412071080 := by gcongr
    _ ≤ (0.159646479148 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479250309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352384344) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281045162190) :
    parallelOracle 12954 0.011 xi bn cd ≤ 0.160617194455 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12954 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12954 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514829697 : ℝ) ≤ plow 12954 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.815640401484 : ℝ) ≤ √(12954 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281045162190 : ℝ) / (2 * 0.560514829697 * 113.815640401484)) * 0.159646479148 +
        0.281045162190 ^ 2 / (2 * 0.560514829697 * 113.815640401484) := by gcongr
    _ ≤ (0.160617194455 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052479250309) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352384344)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281045162190) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12954 12954 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514829697 : ℝ) ≤ plow 12954 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.815640401484 : ℝ) ≤ √(12954 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12954 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12954 Θ 1.22 ≤ 0.011651302891 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.815640401484 := by gcongr <;> linarith
      _ ≤ (0.011651302891 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12954 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12954 12954 0.011 ≤ 0.008398555363 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12954 12954 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12954 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12954 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12954 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12954 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160617194455 + 0.011651302891 + (0.008398555363 : ℝ) *
        (1 + 2 * (0.281045162190 + 0.011651302891) / (0.560514829697 * 113.815640401484))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12954]

end BstLean.Part269.N12954

/-! The original eight local profiles supply actual 12954 moment certificates. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12954 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052479250309 ∧
    0 ≤ bN 12954 BstLean.Part154.csC (groupTheta g) ∧ bN 12954 BstLean.Part154.csC (groupTheta g) ≤ 0.001352384344 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12954 12954 0.011
      (momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12954 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12954 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12954 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229083500735 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12954 0.011
      (momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12954 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12954
/-! The actual computed-centre upper energy formula at 12954. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12954

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12954)
open BstLean.Part268 (cell12954)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084781714471
  | 2 => 0.085712145001
  | 3 => 0.086639033286
  | 4 => 0.087563402406
  | 5 => 0.088486501588
  | 6 => 0.089409841268
  | 7 => 0.090335231729
  | 8 => 0.091264825401
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12954 12954 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12954 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12954

/-! Actual upper energy certificates on all 43 source endpoints at 12954. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12954)
open BstLean.Part268 (cell12954)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12954 (gMinus 12954) (1 - (cell12954 i).lower) ≤ 1 ∧
    energyUpper 12954 (gMinus 12954) (BstLean.Part211.gPlus 12954)
      (finiteEnergy 12954 12954 0.011) (1 - (cell12954 i).lower) ≤
      (cell12954 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨10,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨11,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨12,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨13,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨14,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨15,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨16,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨17,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨18,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨19,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨20,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨21,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨22,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨23,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨24,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨25,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨26,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨27,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨28,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨29,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨30,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨31,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨32,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨33,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨34,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨35,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨36,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨37,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨38,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨39,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨40,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨41,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨42,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨43,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨44,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨45,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨46,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨47,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨48,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨49,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨50,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨51,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12954) (by norm_num)
        (q := 1 - (cell12954 ⟨52,by decide⟩).lower)
        (by norm_num [cell12954]) (by norm_num [cell12954])
      exact ⟨E.1,E.2.trans (by norm_num [cell12954])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12954

/-! Source-cell containment and simple scalar guards at 12954. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12954)
open BstLean.Part268 (cell12954)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12954 ⟨10,by decide⟩).lower ∧ (cell12954 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12954 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12954 ⟨11,by decide⟩).lower ∧ (cell12954 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12954 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12954 ⟨12,by decide⟩).lower ∧ (cell12954 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12954 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12954 ⟨13,by decide⟩).lower ∧ (cell12954 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12954 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12954 ⟨14,by decide⟩).lower ∧ (cell12954 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12954 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12954 ⟨15,by decide⟩).lower ∧ (cell12954 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12954 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12954 ⟨16,by decide⟩).lower ∧ (cell12954 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12954 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12954 ⟨17,by decide⟩).lower ∧ (cell12954 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12954 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12954 ⟨18,by decide⟩).lower ∧ (cell12954 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12954 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12954 ⟨19,by decide⟩).lower ∧ (cell12954 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12954 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12954 ⟨20,by decide⟩).lower ∧ (cell12954 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12954 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12954 ⟨21,by decide⟩).lower ∧ (cell12954 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12954 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12954 ⟨22,by decide⟩).lower ∧ (cell12954 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12954 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12954 ⟨23,by decide⟩).lower ∧ (cell12954 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12954 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12954 ⟨24,by decide⟩).lower ∧ (cell12954 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12954 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12954 ⟨25,by decide⟩).lower ∧ (cell12954 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12954 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12954 ⟨26,by decide⟩).lower ∧ (cell12954 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12954 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12954 ⟨27,by decide⟩).lower ∧ (cell12954 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12954 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12954 ⟨28,by decide⟩).lower ∧ (cell12954 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12954 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12954 ⟨29,by decide⟩).lower ∧ (cell12954 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12954 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12954 ⟨30,by decide⟩).lower ∧ (cell12954 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12954 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12954 ⟨31,by decide⟩).lower ∧ (cell12954 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12954 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12954 ⟨32,by decide⟩).lower ∧ (cell12954 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12954 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12954 ⟨33,by decide⟩).lower ∧ (cell12954 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12954 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12954 ⟨34,by decide⟩).lower ∧ (cell12954 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12954 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12954 ⟨35,by decide⟩).lower ∧ (cell12954 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12954 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12954 ⟨36,by decide⟩).lower ∧ (cell12954 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12954 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12954 ⟨37,by decide⟩).lower ∧ (cell12954 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12954 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12954 ⟨38,by decide⟩).lower ∧ (cell12954 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12954 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12954 ⟨39,by decide⟩).lower ∧ (cell12954 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12954 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12954 ⟨40,by decide⟩).lower ∧ (cell12954 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12954 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12954 ⟨41,by decide⟩).lower ∧ (cell12954 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12954 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12954 ⟨42,by decide⟩).lower ∧ (cell12954 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12954 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12954 ⟨43,by decide⟩).lower ∧ (cell12954 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12954 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12954 ⟨44,by decide⟩).lower ∧ (cell12954 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12954 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12954 ⟨45,by decide⟩).lower ∧ (cell12954 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12954 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12954 ⟨46,by decide⟩).lower ∧ (cell12954 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12954 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12954 ⟨47,by decide⟩).lower ∧ (cell12954 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12954 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12954 ⟨48,by decide⟩).lower ∧ (cell12954 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12954 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12954 ⟨49,by decide⟩).lower ∧ (cell12954 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12954 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12954 ⟨50,by decide⟩).lower ∧ (cell12954 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12954 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12954 ⟨51,by decide⟩).lower ∧ (cell12954 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12954 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12954 ⟨52,by decide⟩).lower ∧ (cell12954 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12954 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12954 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12954 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12954,cell12954,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12954 i).lower ∧
    (cell12954 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12954 i).upper ≤ (0.532 : ℝ) ∧
    (cell12954 i).centre ≤ (0.1 : ℝ) ∧ (cell12954 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12954 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12954 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12954

/-! The local source numeric instances at 12954 have no network premises. -/
namespace BstLean.Part269.N12954
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12954)
open BstLean.Part268 (cell12954)

noncomputable def sourceNumerics12954 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12954 (cell12954 i)
      scalarRow12954.M scalarRow12954.H scalarRow12954.xi := by
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
    energy_allowance := scalarRow12954.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12954]
    centre_nonneg := (scalarRow12954.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12954])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12954
/-! Actual 12955 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12955 ≤ (1.035451959363 : ℝ) := by
  have hr : (113.820033386043 : ℝ) ≤ √(12955 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.820033386043 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12955 12955 (11 / 1000) ≤
    (0.008398231211 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12955) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.820033386043 : ℝ) ≤ √(12955 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12955)
  have hdiv : K / √(12955 : ℝ) ≤ K / 113.820033386043 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.820033386043 ≤ (0.008398231211 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12955.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12955 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12955 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12955 := gPlus_lower 12955
end BstLean.Part269.N12955

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12955
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035451959362 : ℝ) ≤ wn 12955 := by
  have hn : √(12955 : ℝ) ≤ 113.820033386044 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12955 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.820033386044 ≤ 2 / √(12955 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246837801 : ℝ) ≤ rhoBar 12955 BstLean.Part154.csC ∧
    rhoBar 12955 BstLean.Part154.csC ≤ 0.000246838183 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035451959362 : ℝ) / (1.295212 * 12955) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035451959363 : ℝ) / (1.29521 * 12955) := by gcongr
      _ ≤ (0.000246838183 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12955 BstLean.Part154.csC) ≤ 0.000987413662 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12955 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) ≤ 0.000188536494 ∧
    cc1 (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) ≤ 0.000119967059 ∧
    cc2 (rhoBar 12955 BstLean.Part154.csC) ≤ 0.000069641841 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12955 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12955 BstLean.Part154.csC * nuR (rhoBar 12955 BstLean.Part154.csC)) ≤ 0.000493691599 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246838183 : ℝ) * 0.000987413662 := by gcongr
      _ ≤ (0.000493691599 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12955 BstLean.Part154.csC) * nuR (rhoBar 12955 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987413662 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12955 BstLean.Part154.csC) * rhoBar 12955 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246838183 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246838183 / 2 + 0.399 * 0.000987413662 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188536494 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493691599 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119967059 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246838183 / 1.414213562 := by gcongr
      _ ≤ (0.000069641841 : ℝ) := by norm_num

end BstLean.Part269.N12955

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12955
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) ≤ 1.53506E-7 := by
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12955 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12955 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188536494 : ℝ) ^ 2 + 0.000119967059 ^ 2 + 3 * 0.000069641841 ^ 2 +
        2 * 0.797885 * 0.000188536494 * 0.000119967059 + 2 * 0.000188536494 * 0.000069641841 +
        4 * 0.797885 * 0.000119967059 * 0.000069641841 := by gcongr
    _ ≤ (1.53506E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12955 BstLean.Part154.csC Θ ≤ 0.002575749547 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12955 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12955 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035451959363 * 1.53506E-7 / (0.000246837801 : ℝ) := by gcongr
    _ ≤ 0.002575749547 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12955 BstLean.Part154.csC Θ ≤ 0.002856952714 + 0.000650852384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12955 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035451959363 : ℝ) * ((2 * Θ * 0.000246838183 +
        (6863 / 10000) * 0.000246838183 * 12955 * 0.000987413662) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002856952714 + 0.000650852384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12955 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12955 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12955 0.011 Θ ∧ gammaRatio 12955 0.011 Θ ≤ 0.000084856584 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12955 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035451959363 : ℝ) * 0.525 / ((1 - 0.011) * 12955) := by gcongr
      _ ≤ (0.000084856584 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12955 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12955 0.011 Θ) :=
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
    badAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12955 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12955 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12955 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12955 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12955 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12955 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12955 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12955 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12955 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12955 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035451959363 : ℝ) * 12955 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003278309191 + 0.003226601931 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12955

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12955
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12955 BstLean.Part154.csC) (piBar (rhoBar 12955 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12955 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12955 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12955 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12955 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12955 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12955 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12955 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12955 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12955 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051959634417 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12955) ≤ 0.010492332023 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12955 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035451959363)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010492332023 + 2 * 0.737676 / 12955) := by gcongr
    _ ≤ (0.051959634417 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12955 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12955

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12955
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514873160 : ℝ) ≤ plow 12955 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12955) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478875205)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352268513) : eMP 12955 0.011 xi bn ≤ 0.001164515197 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12955 : ℝ) * (1 - 0.011))) ≤ 0.000575823751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352268513 / (12955 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575823751 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575823751 : ℝ) + 3.141593 * 0.052478875205 / (12955 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164515197 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478875205)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352268513) : PiBarMP 12955 12 0.011 xi bn ≤ 0.159640154835 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12955 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036773203736 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.192292140410 : ℝ) ≤ √((12955 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.820033386043 : ℝ) ≤ √(12955 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12955) ≤ 0.122407346478 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036773203736 + 0.052478875205 * 1.772454 / (2 * (113.192292140410 : ℝ))) * (1 + 0.001164515197) +
        8 / (12955 * 113.820033386043) + 0.122407346478 := by gcongr
    _ ≤ (0.159640154835 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478875205)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352268513) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281042316445) :
    parallelOracle 12955 0.011 xi bn cd ≤ 0.160610802575 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12955 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12955 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514873160 : ℝ) ≤ plow 12955 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.820033386043 : ℝ) ≤ √(12955 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281042316445 : ℝ) / (2 * 0.560514873160 * 113.820033386043)) * 0.159640154835 +
        0.281042316445 ^ 2 / (2 * 0.560514873160 * 113.820033386043) := by gcongr
    _ ≤ (0.160610802575 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478875205) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352268513)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281042316445) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12955 12955 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514873160 : ℝ) ≤ plow 12955 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.820033386043 : ℝ) ≤ √(12955 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12955 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12955 Θ 1.22 ≤ 0.011650853199 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.820033386043 := by gcongr <;> linarith
      _ ≤ (0.011650853199 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12955 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12955 12955 0.011 ≤ 0.008398231211 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12955 12955 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12955 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12955 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12955 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12955 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160610802575 + 0.011650853199 + (0.008398231211 : ℝ) *
        (1 + 2 * (0.281042316445 + 0.011650853199) / (0.560514873160 * 113.820033386043))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12955]

end BstLean.Part269.N12955

/-! The original eight local profiles supply actual 12955 moment certificates. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12955 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052478875205 ∧
    0 ≤ bN 12955 BstLean.Part154.csC (groupTheta g) ∧ bN 12955 BstLean.Part154.csC (groupTheta g) ≤ 0.001352268513 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12955 12955 0.011
      (momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12955 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12955 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12955 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229082682028 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12955 0.011
      (momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12955 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12955
/-! The actual computed-centre upper energy formula at 12955. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12955

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12955)
open BstLean.Part268 (cell12955)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084779042065
  | 2 => 0.085709428668
  | 3 => 0.086636267480
  | 4 => 0.087560580248
  | 5 => 0.088483614625
  | 6 => 0.089406879195
  | 7 => 0.090332182077
  | 8 => 0.091261673192
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12955 12955 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12955 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12955

/-! Actual upper energy certificates on all 43 source endpoints at 12955. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12955)
open BstLean.Part268 (cell12955)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12955 (gMinus 12955) (1 - (cell12955 i).lower) ≤ 1 ∧
    energyUpper 12955 (gMinus 12955) (BstLean.Part211.gPlus 12955)
      (finiteEnergy 12955 12955 0.011) (1 - (cell12955 i).lower) ≤
      (cell12955 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨10,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨11,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨12,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨13,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨14,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨15,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨16,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨17,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨18,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨19,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨20,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨21,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨22,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨23,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨24,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨25,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨26,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨27,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨28,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨29,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨30,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨31,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨32,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨33,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨34,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨35,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨36,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨37,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨38,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨39,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨40,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨41,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨42,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨43,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨44,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨45,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨46,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨47,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨48,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨49,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨50,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨51,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12955) (by norm_num)
        (q := 1 - (cell12955 ⟨52,by decide⟩).lower)
        (by norm_num [cell12955]) (by norm_num [cell12955])
      exact ⟨E.1,E.2.trans (by norm_num [cell12955])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12955

/-! Source-cell containment and simple scalar guards at 12955. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12955)
open BstLean.Part268 (cell12955)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12955 ⟨10,by decide⟩).lower ∧ (cell12955 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12955 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12955 ⟨11,by decide⟩).lower ∧ (cell12955 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12955 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12955 ⟨12,by decide⟩).lower ∧ (cell12955 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12955 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12955 ⟨13,by decide⟩).lower ∧ (cell12955 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12955 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12955 ⟨14,by decide⟩).lower ∧ (cell12955 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12955 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12955 ⟨15,by decide⟩).lower ∧ (cell12955 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12955 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12955 ⟨16,by decide⟩).lower ∧ (cell12955 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12955 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12955 ⟨17,by decide⟩).lower ∧ (cell12955 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12955 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12955 ⟨18,by decide⟩).lower ∧ (cell12955 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12955 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12955 ⟨19,by decide⟩).lower ∧ (cell12955 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12955 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12955 ⟨20,by decide⟩).lower ∧ (cell12955 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12955 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12955 ⟨21,by decide⟩).lower ∧ (cell12955 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12955 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12955 ⟨22,by decide⟩).lower ∧ (cell12955 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12955 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12955 ⟨23,by decide⟩).lower ∧ (cell12955 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12955 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12955 ⟨24,by decide⟩).lower ∧ (cell12955 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12955 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12955 ⟨25,by decide⟩).lower ∧ (cell12955 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12955 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12955 ⟨26,by decide⟩).lower ∧ (cell12955 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12955 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12955 ⟨27,by decide⟩).lower ∧ (cell12955 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12955 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12955 ⟨28,by decide⟩).lower ∧ (cell12955 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12955 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12955 ⟨29,by decide⟩).lower ∧ (cell12955 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12955 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12955 ⟨30,by decide⟩).lower ∧ (cell12955 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12955 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12955 ⟨31,by decide⟩).lower ∧ (cell12955 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12955 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12955 ⟨32,by decide⟩).lower ∧ (cell12955 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12955 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12955 ⟨33,by decide⟩).lower ∧ (cell12955 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12955 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12955 ⟨34,by decide⟩).lower ∧ (cell12955 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12955 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12955 ⟨35,by decide⟩).lower ∧ (cell12955 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12955 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12955 ⟨36,by decide⟩).lower ∧ (cell12955 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12955 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12955 ⟨37,by decide⟩).lower ∧ (cell12955 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12955 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12955 ⟨38,by decide⟩).lower ∧ (cell12955 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12955 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12955 ⟨39,by decide⟩).lower ∧ (cell12955 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12955 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12955 ⟨40,by decide⟩).lower ∧ (cell12955 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12955 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12955 ⟨41,by decide⟩).lower ∧ (cell12955 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12955 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12955 ⟨42,by decide⟩).lower ∧ (cell12955 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12955 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12955 ⟨43,by decide⟩).lower ∧ (cell12955 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12955 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12955 ⟨44,by decide⟩).lower ∧ (cell12955 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12955 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12955 ⟨45,by decide⟩).lower ∧ (cell12955 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12955 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12955 ⟨46,by decide⟩).lower ∧ (cell12955 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12955 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12955 ⟨47,by decide⟩).lower ∧ (cell12955 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12955 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12955 ⟨48,by decide⟩).lower ∧ (cell12955 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12955 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12955 ⟨49,by decide⟩).lower ∧ (cell12955 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12955 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12955 ⟨50,by decide⟩).lower ∧ (cell12955 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12955 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12955 ⟨51,by decide⟩).lower ∧ (cell12955 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12955 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12955 ⟨52,by decide⟩).lower ∧ (cell12955 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12955 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12955 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12955 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12955,cell12955,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12955 i).lower ∧
    (cell12955 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12955 i).upper ≤ (0.532 : ℝ) ∧
    (cell12955 i).centre ≤ (0.1 : ℝ) ∧ (cell12955 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12955 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12955 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12955

/-! The local source numeric instances at 12955 have no network premises. -/
namespace BstLean.Part269.N12955
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12955)
open BstLean.Part268 (cell12955)

noncomputable def sourceNumerics12955 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12955 (cell12955 i)
      scalarRow12955.M scalarRow12955.H scalarRow12955.xi := by
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
    energy_allowance := scalarRow12955.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12955]
    centre_nonneg := (scalarRow12955.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12955])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12955
/-! Actual 12956 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12956 ≤ (1.035450579254 : ℝ) := by
  have hr : (113.824426201057 : ℝ) ≤ √(12956 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.824426201057 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12956 12956 (11 / 1000) ≤
    (0.008397907096 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12956) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.824426201057 : ℝ) ≤ √(12956 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12956)
  have hdiv : K / √(12956 : ℝ) ≤ K / 113.824426201057 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.824426201057 ≤ (0.008397907096 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12956.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12956 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12956 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12956 := gPlus_lower 12956
end BstLean.Part269.N12956

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12956
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035450579253 : ℝ) ≤ wn 12956 := by
  have hn : √(12956 : ℝ) ≤ 113.824426201058 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12956 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.824426201058 ≤ 2 / √(12956 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246818420 : ℝ) ≤ rhoBar 12956 BstLean.Part154.csC ∧
    rhoBar 12956 BstLean.Part154.csC ≤ 0.000246818802 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035450579253 : ℝ) / (1.295212 * 12956) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035450579254 : ℝ) / (1.29521 * 12956) := by gcongr
      _ ≤ (0.000246818802 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12956 BstLean.Part154.csC) ≤ 0.000987336128 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12956 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) ≤ 0.000188521690 ∧
    cc1 (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) ≤ 0.000119957639 ∧
    cc2 (rhoBar 12956 BstLean.Part154.csC) ≤ 0.000069636373 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12956 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12956 BstLean.Part154.csC * nuR (rhoBar 12956 BstLean.Part154.csC)) ≤ 0.000493652834 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246818802 : ℝ) * 0.000987336128 := by gcongr
      _ ≤ (0.000493652834 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12956 BstLean.Part154.csC) * nuR (rhoBar 12956 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987336128 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12956 BstLean.Part154.csC) * rhoBar 12956 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246818802 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246818802 / 2 + 0.399 * 0.000987336128 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188521690 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493652834 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119957639 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246818802 / 1.414213562 := by gcongr
      _ ≤ (0.000069636373 : ℝ) := by norm_num

end BstLean.Part269.N12956

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12956
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) ≤ 1.53482E-7 := by
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12956 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12956 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188521690 : ℝ) ^ 2 + 0.000119957639 ^ 2 + 3 * 0.000069636373 ^ 2 +
        2 * 0.797885 * 0.000188521690 * 0.000119957639 + 2 * 0.000188521690 * 0.000069636373 +
        4 * 0.797885 * 0.000119957639 * 0.000069636373 := by gcongr
    _ ≤ (1.53482E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12956 BstLean.Part154.csC Θ ≤ 0.002575545631 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12956 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12956 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035450579254 * 1.53482E-7 / (0.000246818420 : ℝ) := by gcongr
    _ ≤ 0.002575545631 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12956 BstLean.Part154.csC Θ ≤ 0.002856720764 + 0.000650800414 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12956 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035450579254 : ℝ) * ((2 * Θ * 0.000246818802 +
        (6863 / 10000) * 0.000246818802 * 12956 * 0.000987336128) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002856720764 + 0.000650800414 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12956 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12956 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12956 0.011 Θ ∧ gammaRatio 12956 0.011 Θ ≤ 0.000084849922 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12956 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035450579254 : ℝ) * 0.525 / ((1 - 0.011) * 12956) := by gcongr
      _ ≤ (0.000084849922 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12956 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12956 0.011 Θ) :=
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
    badAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12956 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12956 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12956 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12956 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12956 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12956 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12956 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12956 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12956 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12956 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035450579254 : ℝ) * 12956 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003278077241 + 0.003226346045 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12956

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12956
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12956 BstLean.Part154.csC) (piBar (rhoBar 12956 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12956 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12956 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12956 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12956 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12956 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12956 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12956 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12956 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12956 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051957607612 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12956) ≤ 0.010491927093 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12956 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035450579254)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010491927093 + 2 * 0.737676 / 12956) := by gcongr
    _ ≤ (0.051957607612 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12956 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12956

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12956
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514916617 : ℝ) ≤ plow 12956 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12956) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478508915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352161457) : eMP 12956 0.011 xi bn ≤ 0.001164424082 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12956 : ℝ) * (1 - 0.011))) ≤ 0.000575778735 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352161457 / (12956 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575778735 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575778735 : ℝ) + 3.141593 * 0.052478508915 / (12956 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164424082 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478508915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352161457) : PiBarMP 12956 12 0.011 xi bn ≤ 0.159633950668 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12956 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036771748082 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.196660728132 : ℝ) ≤ √((12956 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.824426201057 : ℝ) ≤ √(12956 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12956) ≤ 0.122402622423 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036771748082 + 0.052478508915 * 1.772454 / (2 * (113.196660728132 : ℝ))) * (1 + 0.001164424082) +
        8 / (12956 * 113.824426201057) + 0.122402622423 := by gcongr
    _ ≤ (0.159633950668 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478508915)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352161457) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281039490168) :
    parallelOracle 12956 0.011 xi bn cd ≤ 0.160604531222 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12956 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12956 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514916617 : ℝ) ≤ plow 12956 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.824426201057 : ℝ) ≤ √(12956 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281039490168 : ℝ) / (2 * 0.560514916617 * 113.824426201057)) * 0.159633950668 +
        0.281039490168 ^ 2 / (2 * 0.560514916617 * 113.824426201057) := by gcongr
    _ ≤ (0.160604531222 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478508915) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352161457)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281039490168) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12956 12956 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514916617 : ℝ) ≤ plow 12956 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.824426201057 : ℝ) ≤ √(12956 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12956 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12956 Θ 1.22 ≤ 0.011650403558 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.824426201057 := by gcongr <;> linarith
      _ ≤ (0.011650403558 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12956 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12956 12956 0.011 ≤ 0.008397907096 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12956 12956 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12956 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12956 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12956 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12956 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160604531222 + 0.011650403558 + (0.008397907096 : ℝ) *
        (1 + 2 * (0.281039490168 + 0.011650403558) / (0.560514916617 * 113.824426201057))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12956]

end BstLean.Part269.N12956

/-! The original eight local profiles supply actual 12956 moment certificates. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12956 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052478508915 ∧
    0 ≤ bN 12956 BstLean.Part154.csC (groupTheta g) ∧ bN 12956 BstLean.Part154.csC (groupTheta g) ≤ 0.001352161457 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12956 12956 0.011
      (momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12956 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12956 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12956 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229081882556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12956 0.011
      (momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12956 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12956
/-! The actual computed-centre upper energy formula at 12956. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12956

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12956)
open BstLean.Part268 (cell12956)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084776370505
  | 2 => 0.085706713212
  | 3 => 0.086633502590
  | 4 => 0.087557759056
  | 5 => 0.088480728688
  | 6 => 0.089403918220
  | 7 => 0.090329133611
  | 8 => 0.091258522276
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12956 12956 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12956 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12956

/-! Actual upper energy certificates on all 43 source endpoints at 12956. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12956)
open BstLean.Part268 (cell12956)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12956 (gMinus 12956) (1 - (cell12956 i).lower) ≤ 1 ∧
    energyUpper 12956 (gMinus 12956) (BstLean.Part211.gPlus 12956)
      (finiteEnergy 12956 12956 0.011) (1 - (cell12956 i).lower) ≤
      (cell12956 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨10,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨11,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨12,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨13,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨14,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨15,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨16,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨17,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨18,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨19,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨20,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨21,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨22,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨23,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨24,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨25,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨26,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨27,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨28,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨29,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨30,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨31,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨32,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨33,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨34,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨35,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨36,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨37,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨38,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨39,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨40,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨41,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨42,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨43,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨44,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨45,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨46,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨47,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨48,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨49,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨50,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨51,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12956) (by norm_num)
        (q := 1 - (cell12956 ⟨52,by decide⟩).lower)
        (by norm_num [cell12956]) (by norm_num [cell12956])
      exact ⟨E.1,E.2.trans (by norm_num [cell12956])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12956

/-! Source-cell containment and simple scalar guards at 12956. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12956)
open BstLean.Part268 (cell12956)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12956 ⟨10,by decide⟩).lower ∧ (cell12956 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12956 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12956 ⟨11,by decide⟩).lower ∧ (cell12956 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12956 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12956 ⟨12,by decide⟩).lower ∧ (cell12956 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12956 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12956 ⟨13,by decide⟩).lower ∧ (cell12956 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12956 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12956 ⟨14,by decide⟩).lower ∧ (cell12956 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12956 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12956 ⟨15,by decide⟩).lower ∧ (cell12956 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12956 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12956 ⟨16,by decide⟩).lower ∧ (cell12956 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12956 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12956 ⟨17,by decide⟩).lower ∧ (cell12956 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12956 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12956 ⟨18,by decide⟩).lower ∧ (cell12956 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12956 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12956 ⟨19,by decide⟩).lower ∧ (cell12956 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12956 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12956 ⟨20,by decide⟩).lower ∧ (cell12956 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12956 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12956 ⟨21,by decide⟩).lower ∧ (cell12956 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12956 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12956 ⟨22,by decide⟩).lower ∧ (cell12956 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12956 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12956 ⟨23,by decide⟩).lower ∧ (cell12956 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12956 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12956 ⟨24,by decide⟩).lower ∧ (cell12956 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12956 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12956 ⟨25,by decide⟩).lower ∧ (cell12956 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12956 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12956 ⟨26,by decide⟩).lower ∧ (cell12956 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12956 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12956 ⟨27,by decide⟩).lower ∧ (cell12956 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12956 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12956 ⟨28,by decide⟩).lower ∧ (cell12956 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12956 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12956 ⟨29,by decide⟩).lower ∧ (cell12956 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12956 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12956 ⟨30,by decide⟩).lower ∧ (cell12956 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12956 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12956 ⟨31,by decide⟩).lower ∧ (cell12956 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12956 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12956 ⟨32,by decide⟩).lower ∧ (cell12956 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12956 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12956 ⟨33,by decide⟩).lower ∧ (cell12956 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12956 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12956 ⟨34,by decide⟩).lower ∧ (cell12956 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12956 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12956 ⟨35,by decide⟩).lower ∧ (cell12956 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12956 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12956 ⟨36,by decide⟩).lower ∧ (cell12956 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12956 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12956 ⟨37,by decide⟩).lower ∧ (cell12956 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12956 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12956 ⟨38,by decide⟩).lower ∧ (cell12956 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12956 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12956 ⟨39,by decide⟩).lower ∧ (cell12956 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12956 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12956 ⟨40,by decide⟩).lower ∧ (cell12956 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12956 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12956 ⟨41,by decide⟩).lower ∧ (cell12956 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12956 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12956 ⟨42,by decide⟩).lower ∧ (cell12956 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12956 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12956 ⟨43,by decide⟩).lower ∧ (cell12956 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12956 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12956 ⟨44,by decide⟩).lower ∧ (cell12956 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12956 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12956 ⟨45,by decide⟩).lower ∧ (cell12956 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12956 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12956 ⟨46,by decide⟩).lower ∧ (cell12956 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12956 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12956 ⟨47,by decide⟩).lower ∧ (cell12956 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12956 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12956 ⟨48,by decide⟩).lower ∧ (cell12956 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12956 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12956 ⟨49,by decide⟩).lower ∧ (cell12956 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12956 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12956 ⟨50,by decide⟩).lower ∧ (cell12956 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12956 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12956 ⟨51,by decide⟩).lower ∧ (cell12956 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12956 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12956 ⟨52,by decide⟩).lower ∧ (cell12956 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12956 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12956 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12956 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12956,cell12956,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12956 i).lower ∧
    (cell12956 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12956 i).upper ≤ (0.532 : ℝ) ∧
    (cell12956 i).centre ≤ (0.1 : ℝ) ∧ (cell12956 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12956 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12956 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12956

/-! The local source numeric instances at 12956 have no network premises. -/
namespace BstLean.Part269.N12956
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12956)
open BstLean.Part268 (cell12956)

noncomputable def sourceNumerics12956 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12956 (cell12956 i)
      scalarRow12956.M scalarRow12956.H scalarRow12956.xi := by
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
    energy_allowance := scalarRow12956.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12956]
    centre_nonneg := (scalarRow12956.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12956])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12956
/-! Actual 12957 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12957 ≤ (1.035449199305 : ℝ) := by
  have hr : (113.828818846546 : ℝ) ≤ √(12957 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.828818846546 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12957 12957 (11 / 1000) ≤
    (0.008397583019 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12957) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.828818846546 : ℝ) ≤ √(12957 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12957)
  have hdiv : K / √(12957 : ℝ) ≤ K / 113.828818846546 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.828818846546 ≤ (0.008397583019 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12957.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12957 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12957 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12957 := gPlus_lower 12957
end BstLean.Part269.N12957

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12957
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035449199304 : ℝ) ≤ wn 12957 := by
  have hn : √(12957 : ℝ) ≤ 113.828818846547 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12957 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.828818846547 ≤ 2 / √(12957 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246799042 : ℝ) ≤ rhoBar 12957 BstLean.Part154.csC ∧
    rhoBar 12957 BstLean.Part154.csC ≤ 0.000246799424 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035449199304 : ℝ) / (1.295212 * 12957) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035449199305 : ℝ) / (1.29521 * 12957) := by gcongr
      _ ≤ (0.000246799424 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12957 BstLean.Part154.csC) ≤ 0.000987258606 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12957 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) ≤ 0.000188506888 ∧
    cc1 (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) ≤ 0.000119948221 ∧
    cc2 (rhoBar 12957 BstLean.Part154.csC) ≤ 0.000069630905 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12957 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12957 BstLean.Part154.csC * nuR (rhoBar 12957 BstLean.Part154.csC)) ≤ 0.000493614076 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246799424 : ℝ) * 0.000987258606 := by gcongr
      _ ≤ (0.000493614076 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12957 BstLean.Part154.csC) * nuR (rhoBar 12957 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987258606 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12957 BstLean.Part154.csC) * rhoBar 12957 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246799424 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246799424 / 2 + 0.399 * 0.000987258606 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188506888 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493614076 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119948221 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246799424 / 1.414213562 := by gcongr
      _ ≤ (0.000069630905 : ℝ) := by norm_num

end BstLean.Part269.N12957

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12957
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) ≤ 1.53458E-7 := by
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12957 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12957 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188506888 : ℝ) ^ 2 + 0.000119948221 ^ 2 + 3 * 0.000069630905 ^ 2 +
        2 * 0.797885 * 0.000188506888 * 0.000119948221 + 2 * 0.000188506888 * 0.000069630905 +
        4 * 0.797885 * 0.000119948221 * 0.000069630905 := by gcongr
    _ ≤ (1.53458E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12957 BstLean.Part154.csC Θ ≤ 0.002575341654 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12957 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12957 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035449199305 * 1.53458E-7 / (0.000246799042 : ℝ) := by gcongr
    _ ≤ 0.002575341654 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12957 BstLean.Part154.csC Θ ≤ 0.002856488851 + 0.000650748452 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12957 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035449199305 : ℝ) * ((2 * Θ * 0.000246799424 +
        (6863 / 10000) * 0.000246799424 * 12957 * 0.000987258606) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002856488851 + 0.000650748452 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12957 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12957 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12957 0.011 Θ ∧ gammaRatio 12957 0.011 Θ ≤ 0.000084843260 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12957 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035449199305 : ℝ) * 0.525 / ((1 - 0.011) * 12957) := by gcongr
      _ ≤ (0.000084843260 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12957 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12957 0.011 Θ) :=
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
    badAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12957 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12957 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12957 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12957 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12957 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12957 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12957 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12957 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12957 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12957 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035449199305 : ℝ) * 12957 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003277845328 + 0.003226090106 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12957

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12957
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12957 BstLean.Part154.csC) (piBar (rhoBar 12957 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12957 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12957 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12957 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12957 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12957 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12957 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12957 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12957 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12957 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051955581043 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12957) ≤ 0.010491522210 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12957 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035449199305)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010491522210 + 2 * 0.737676 / 12957) := by gcongr
    _ ≤ (0.051955581043 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12957 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12957

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12957
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514960067 : ℝ) ≤ plow 12957 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12957) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478142634)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352054369) : eMP 12957 0.011 xi bn ≤ 0.001164332961 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12957 : ℝ) * (1 - 0.011))) ≤ 0.000575733716 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001352054369 / (12957 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575733716 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575733716 : ℝ) + 3.141593 * 0.052478142634 / (12957 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164332961 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478142634)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352054369) : PiBarMP 12957 12 0.011 xi bn ≤ 0.159627746558 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12957 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036770291936 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.201029147265 : ℝ) ≤ √((12957 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.828818846546 : ℝ) ≤ √(12957 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12957) ≤ 0.122397898915 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036770291936 + 0.052478142634 * 1.772454 / (2 * (113.201029147265 : ℝ))) * (1 + 0.001164332961) +
        8 / (12957 * 113.828818846546) + 0.122397898915 := by gcongr
    _ ≤ (0.159627746558 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478142634)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352054369) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281036664143) :
    parallelOracle 12957 0.011 xi bn cd ≤ 0.160598259935 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12957 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12957 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514960067 : ℝ) ≤ plow 12957 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.828818846546 : ℝ) ≤ √(12957 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281036664143 : ℝ) / (2 * 0.560514960067 * 113.828818846546)) * 0.159627746558 +
        0.281036664143 ^ 2 / (2 * 0.560514960067 * 113.828818846546) := by gcongr
    _ ≤ (0.160598259935 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052478142634) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001352054369)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281036664143) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12957 12957 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514960067 : ℝ) ≤ plow 12957 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.828818846546 : ℝ) ≤ √(12957 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12957 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12957 Θ 1.22 ≤ 0.011649953970 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.828818846546 := by gcongr <;> linarith
      _ ≤ (0.011649953970 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12957 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12957 12957 0.011 ≤ 0.008397583019 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12957 12957 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12957 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12957 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12957 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12957 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160598259935 + 0.011649953970 + (0.008397583019 : ℝ) *
        (1 + 2 * (0.281036664143 + 0.011649953970) / (0.560514960067 * 113.828818846546))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12957]

end BstLean.Part269.N12957

/-! The original eight local profiles supply actual 12957 moment certificates. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12957 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052478142634 ∧
    0 ≤ bN 12957 BstLean.Part154.csC (groupTheta g) ∧ bN 12957 BstLean.Part154.csC (groupTheta g) ≤ 0.001352054369 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12957 12957 0.011
      (momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12957 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12957 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12957 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229081083100 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12957 0.011
      (momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12957 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12957
/-! The actual computed-centre upper energy formula at 12957. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12957

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12957)
open BstLean.Part268 (cell12957)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084773699788
  | 2 => 0.085703998633
  | 3 => 0.086630738616
  | 4 => 0.087554938828
  | 5 => 0.088477843774
  | 6 => 0.089400958341
  | 7 => 0.090326086330
  | 8 => 0.091255372650
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12957 12957 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12957 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12957

/-! Actual upper energy certificates on all 43 source endpoints at 12957. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12957)
open BstLean.Part268 (cell12957)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12957 (gMinus 12957) (1 - (cell12957 i).lower) ≤ 1 ∧
    energyUpper 12957 (gMinus 12957) (BstLean.Part211.gPlus 12957)
      (finiteEnergy 12957 12957 0.011) (1 - (cell12957 i).lower) ≤
      (cell12957 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨10,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨11,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨12,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨13,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨14,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨15,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨16,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨17,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨18,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨19,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨20,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨21,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨22,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨23,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨24,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨25,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨26,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨27,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨28,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨29,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨30,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨31,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨32,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨33,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨34,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨35,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨36,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨37,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨38,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨39,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨40,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨41,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨42,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨43,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨44,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨45,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨46,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨47,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨48,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨49,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨50,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨51,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12957) (by norm_num)
        (q := 1 - (cell12957 ⟨52,by decide⟩).lower)
        (by norm_num [cell12957]) (by norm_num [cell12957])
      exact ⟨E.1,E.2.trans (by norm_num [cell12957])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12957

/-! Source-cell containment and simple scalar guards at 12957. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12957)
open BstLean.Part268 (cell12957)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12957 ⟨10,by decide⟩).lower ∧ (cell12957 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12957 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12957 ⟨11,by decide⟩).lower ∧ (cell12957 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12957 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12957 ⟨12,by decide⟩).lower ∧ (cell12957 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12957 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12957 ⟨13,by decide⟩).lower ∧ (cell12957 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12957 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12957 ⟨14,by decide⟩).lower ∧ (cell12957 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12957 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12957 ⟨15,by decide⟩).lower ∧ (cell12957 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12957 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12957 ⟨16,by decide⟩).lower ∧ (cell12957 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12957 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12957 ⟨17,by decide⟩).lower ∧ (cell12957 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12957 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12957 ⟨18,by decide⟩).lower ∧ (cell12957 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12957 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12957 ⟨19,by decide⟩).lower ∧ (cell12957 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12957 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12957 ⟨20,by decide⟩).lower ∧ (cell12957 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12957 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12957 ⟨21,by decide⟩).lower ∧ (cell12957 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12957 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12957 ⟨22,by decide⟩).lower ∧ (cell12957 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12957 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12957 ⟨23,by decide⟩).lower ∧ (cell12957 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12957 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12957 ⟨24,by decide⟩).lower ∧ (cell12957 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12957 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12957 ⟨25,by decide⟩).lower ∧ (cell12957 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12957 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12957 ⟨26,by decide⟩).lower ∧ (cell12957 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12957 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12957 ⟨27,by decide⟩).lower ∧ (cell12957 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12957 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12957 ⟨28,by decide⟩).lower ∧ (cell12957 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12957 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12957 ⟨29,by decide⟩).lower ∧ (cell12957 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12957 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12957 ⟨30,by decide⟩).lower ∧ (cell12957 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12957 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12957 ⟨31,by decide⟩).lower ∧ (cell12957 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12957 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12957 ⟨32,by decide⟩).lower ∧ (cell12957 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12957 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12957 ⟨33,by decide⟩).lower ∧ (cell12957 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12957 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12957 ⟨34,by decide⟩).lower ∧ (cell12957 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12957 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12957 ⟨35,by decide⟩).lower ∧ (cell12957 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12957 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12957 ⟨36,by decide⟩).lower ∧ (cell12957 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12957 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12957 ⟨37,by decide⟩).lower ∧ (cell12957 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12957 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12957 ⟨38,by decide⟩).lower ∧ (cell12957 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12957 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12957 ⟨39,by decide⟩).lower ∧ (cell12957 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12957 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12957 ⟨40,by decide⟩).lower ∧ (cell12957 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12957 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12957 ⟨41,by decide⟩).lower ∧ (cell12957 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12957 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12957 ⟨42,by decide⟩).lower ∧ (cell12957 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12957 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12957 ⟨43,by decide⟩).lower ∧ (cell12957 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12957 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12957 ⟨44,by decide⟩).lower ∧ (cell12957 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12957 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12957 ⟨45,by decide⟩).lower ∧ (cell12957 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12957 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12957 ⟨46,by decide⟩).lower ∧ (cell12957 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12957 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12957 ⟨47,by decide⟩).lower ∧ (cell12957 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12957 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12957 ⟨48,by decide⟩).lower ∧ (cell12957 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12957 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12957 ⟨49,by decide⟩).lower ∧ (cell12957 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12957 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12957 ⟨50,by decide⟩).lower ∧ (cell12957 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12957 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12957 ⟨51,by decide⟩).lower ∧ (cell12957 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12957 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12957 ⟨52,by decide⟩).lower ∧ (cell12957 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12957 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12957 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12957 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12957,cell12957,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12957 i).lower ∧
    (cell12957 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12957 i).upper ≤ (0.532 : ℝ) ∧
    (cell12957 i).centre ≤ (0.1 : ℝ) ∧ (cell12957 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12957 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12957 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12957

/-! The local source numeric instances at 12957 have no network premises. -/
namespace BstLean.Part269.N12957
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12957)
open BstLean.Part268 (cell12957)

noncomputable def sourceNumerics12957 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12957 (cell12957 i)
      scalarRow12957.M scalarRow12957.H scalarRow12957.xi := by
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
    energy_allowance := scalarRow12957.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12957]
    centre_nonneg := (scalarRow12957.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12957])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12957
/-! Actual 12958 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12958 ≤ (1.035447819517 : ℝ) := by
  have hr : (113.833211322531 : ℝ) ≤ √(12958 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.833211322531 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12958 12958 (11 / 1000) ≤
    (0.008397258980 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12958) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.833211322531 : ℝ) ≤ √(12958 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12958)
  have hdiv : K / √(12958 : ℝ) ≤ K / 113.833211322531 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.833211322531 ≤ (0.008397258980 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12958.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12958 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12958 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12958 := gPlus_lower 12958
end BstLean.Part269.N12958

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12958
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035447819516 : ℝ) ≤ wn 12958 := by
  have hn : √(12958 : ℝ) ≤ 113.833211322532 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12958 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.833211322532 ≤ 2 / √(12958 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246779667 : ℝ) ≤ rhoBar 12958 BstLean.Part154.csC ∧
    rhoBar 12958 BstLean.Part154.csC ≤ 0.000246780049 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035447819516 : ℝ) / (1.295212 * 12958) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035447819517 : ℝ) / (1.29521 * 12958) := by gcongr
      _ ≤ (0.000246780049 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12958 BstLean.Part154.csC) ≤ 0.000987181097 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12958 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) ≤ 0.000188492089 ∧
    cc1 (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) ≤ 0.000119938804 ∧
    cc2 (rhoBar 12958 BstLean.Part154.csC) ≤ 0.000069625439 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12958 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12958 BstLean.Part154.csC * nuR (rhoBar 12958 BstLean.Part154.csC)) ≤ 0.000493575324 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246780049 : ℝ) * 0.000987181097 := by gcongr
      _ ≤ (0.000493575324 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12958 BstLean.Part154.csC) * nuR (rhoBar 12958 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987181097 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12958 BstLean.Part154.csC) * rhoBar 12958 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246780049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246780049 / 2 + 0.399 * 0.000987181097 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188492089 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493575324 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119938804 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246780049 / 1.414213562 := by gcongr
      _ ≤ (0.000069625439 : ℝ) := by norm_num

end BstLean.Part269.N12958

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12958
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) ≤ 1.53434E-7 := by
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12958 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12958 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188492089 : ℝ) ^ 2 + 0.000119938804 ^ 2 + 3 * 0.000069625439 ^ 2 +
        2 * 0.797885 * 0.000188492089 * 0.000119938804 + 2 * 0.000188492089 * 0.000069625439 +
        4 * 0.797885 * 0.000119938804 * 0.000069625439 := by gcongr
    _ ≤ (1.53434E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12958 BstLean.Part154.csC Θ ≤ 0.002575137615 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12958 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12958 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035447819517 * 1.53434E-7 / (0.000246779667 : ℝ) := by gcongr
    _ ≤ 0.002575137615 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12958 BstLean.Part154.csC Θ ≤ 0.002856256977 + 0.000650696497 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12958 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035447819517 : ℝ) * ((2 * Θ * 0.000246780049 +
        (6863 / 10000) * 0.000246780049 * 12958 * 0.000987181097) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002856256977 + 0.000650696497 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12958 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12958 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12958 0.011 Θ ∧ gammaRatio 12958 0.011 Θ ≤ 0.000084836599 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12958 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035447819517 : ℝ) * 0.525 / ((1 - 0.011) * 12958) := by gcongr
      _ ≤ (0.000084836599 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12958 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12958 0.011 Θ) :=
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
    badAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12958 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12958 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12958 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12958 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12958 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12958 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12958 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12958 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12958 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12958 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035447819517 : ℝ) * 12958 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003277613454 + 0.003225834112 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12958

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12958
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12958 BstLean.Part154.csC) (piBar (rhoBar 12958 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12958 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12958 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12958 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12958 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12958 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12958 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12958 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12958 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12958 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051953554715 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12958) ≤ 0.010491117375 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12958 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035447819517)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010491117375 + 2 * 0.737676 / 12958) := by gcongr
    _ ≤ (0.051953554715 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12958 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12958

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12958
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515003511 : ℝ) ≤ plow 12958 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12958) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477776363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351947248) : eMP 12958 0.011 xi bn ≤ 0.001164241834 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12958 : ℝ) * (1 - 0.011))) ≤ 0.000575688694 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351947248 / (12958 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575688694 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575688694 : ℝ) + 3.141593 * 0.052477776363 / (12958 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164241834 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477776363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351947248) : PiBarMP 12958 12 0.011 xi bn ≤ 0.159621542490 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12958 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036768835283 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.205397397827 : ℝ) ≤ √((12958 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.833211322531 : ℝ) ≤ √(12958 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12958) ≤ 0.122393175954 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036768835283 + 0.052477776363 * 1.772454 / (2 * (113.205397397827 : ℝ))) * (1 + 0.001164241834) +
        8 / (12958 * 113.833211322531) + 0.122393175954 := by gcongr
    _ ≤ (0.159621542490 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477776363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351947248) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281033838378) :
    parallelOracle 12958 0.011 xi bn cd ≤ 0.160591988698 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12958 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12958 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515003511 : ℝ) ≤ plow 12958 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.833211322531 : ℝ) ≤ √(12958 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281033838378 : ℝ) / (2 * 0.560515003511 * 113.833211322531)) * 0.159621542490 +
        0.281033838378 ^ 2 / (2 * 0.560515003511 * 113.833211322531) := by gcongr
    _ ≤ (0.160591988698 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477776363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351947248)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281033838378) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12958 12958 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515003511 : ℝ) ≤ plow 12958 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.833211322531 : ℝ) ≤ √(12958 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12958 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12958 Θ 1.22 ≤ 0.011649504434 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.833211322531 := by gcongr <;> linarith
      _ ≤ (0.011649504434 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12958 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12958 12958 0.011 ≤ 0.008397258980 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12958 12958 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12958 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12958 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12958 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12958 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160591988698 + 0.011649504434 + (0.008397258980 : ℝ) *
        (1 + 2 * (0.281033838378 + 0.011649504434) / (0.560515003511 * 113.833211322531))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12958]

end BstLean.Part269.N12958

/-! The original eight local profiles supply actual 12958 moment certificates. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12958 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052477776363 ∧
    0 ≤ bN 12958 BstLean.Part154.csC (groupTheta g) ∧ bN 12958 BstLean.Part154.csC (groupTheta g) ≤ 0.001351947248 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12958 12958 0.011
      (momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12958 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12958 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12958 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229080283663 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12958 0.011
      (momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12958 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12958
/-! The actual computed-centre upper energy formula at 12958. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12958

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12958)
open BstLean.Part268 (cell12958)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084771029916
  | 2 => 0.085701284929
  | 3 => 0.086627975557
  | 4 => 0.087552119564
  | 5 => 0.088474959884
  | 6 => 0.089397999559
  | 7 => 0.090323040233
  | 8 => 0.091252224315
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12958 12958 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12958 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12958

/-! Actual upper energy certificates on all 43 source endpoints at 12958. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12958)
open BstLean.Part268 (cell12958)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12958 (gMinus 12958) (1 - (cell12958 i).lower) ≤ 1 ∧
    energyUpper 12958 (gMinus 12958) (BstLean.Part211.gPlus 12958)
      (finiteEnergy 12958 12958 0.011) (1 - (cell12958 i).lower) ≤
      (cell12958 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨10,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨11,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨12,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨13,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨14,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨15,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨16,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨17,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨18,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨19,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨20,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨21,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨22,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨23,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨24,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨25,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨26,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨27,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨28,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨29,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨30,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨31,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨32,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨33,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨34,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨35,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨36,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨37,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨38,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨39,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨40,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨41,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨42,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨43,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨44,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨45,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨46,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨47,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨48,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨49,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨50,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨51,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12958) (by norm_num)
        (q := 1 - (cell12958 ⟨52,by decide⟩).lower)
        (by norm_num [cell12958]) (by norm_num [cell12958])
      exact ⟨E.1,E.2.trans (by norm_num [cell12958])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12958

/-! Source-cell containment and simple scalar guards at 12958. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12958)
open BstLean.Part268 (cell12958)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12958 ⟨10,by decide⟩).lower ∧ (cell12958 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12958 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12958 ⟨11,by decide⟩).lower ∧ (cell12958 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12958 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12958 ⟨12,by decide⟩).lower ∧ (cell12958 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12958 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12958 ⟨13,by decide⟩).lower ∧ (cell12958 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12958 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12958 ⟨14,by decide⟩).lower ∧ (cell12958 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12958 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12958 ⟨15,by decide⟩).lower ∧ (cell12958 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12958 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12958 ⟨16,by decide⟩).lower ∧ (cell12958 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12958 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12958 ⟨17,by decide⟩).lower ∧ (cell12958 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12958 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12958 ⟨18,by decide⟩).lower ∧ (cell12958 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12958 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12958 ⟨19,by decide⟩).lower ∧ (cell12958 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12958 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12958 ⟨20,by decide⟩).lower ∧ (cell12958 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12958 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12958 ⟨21,by decide⟩).lower ∧ (cell12958 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12958 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12958 ⟨22,by decide⟩).lower ∧ (cell12958 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12958 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12958 ⟨23,by decide⟩).lower ∧ (cell12958 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12958 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12958 ⟨24,by decide⟩).lower ∧ (cell12958 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12958 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12958 ⟨25,by decide⟩).lower ∧ (cell12958 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12958 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12958 ⟨26,by decide⟩).lower ∧ (cell12958 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12958 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12958 ⟨27,by decide⟩).lower ∧ (cell12958 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12958 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12958 ⟨28,by decide⟩).lower ∧ (cell12958 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12958 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12958 ⟨29,by decide⟩).lower ∧ (cell12958 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12958 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12958 ⟨30,by decide⟩).lower ∧ (cell12958 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12958 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12958 ⟨31,by decide⟩).lower ∧ (cell12958 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12958 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12958 ⟨32,by decide⟩).lower ∧ (cell12958 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12958 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12958 ⟨33,by decide⟩).lower ∧ (cell12958 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12958 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12958 ⟨34,by decide⟩).lower ∧ (cell12958 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12958 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12958 ⟨35,by decide⟩).lower ∧ (cell12958 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12958 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12958 ⟨36,by decide⟩).lower ∧ (cell12958 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12958 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12958 ⟨37,by decide⟩).lower ∧ (cell12958 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12958 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12958 ⟨38,by decide⟩).lower ∧ (cell12958 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12958 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12958 ⟨39,by decide⟩).lower ∧ (cell12958 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12958 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12958 ⟨40,by decide⟩).lower ∧ (cell12958 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12958 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12958 ⟨41,by decide⟩).lower ∧ (cell12958 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12958 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12958 ⟨42,by decide⟩).lower ∧ (cell12958 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12958 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12958 ⟨43,by decide⟩).lower ∧ (cell12958 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12958 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12958 ⟨44,by decide⟩).lower ∧ (cell12958 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12958 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12958 ⟨45,by decide⟩).lower ∧ (cell12958 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12958 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12958 ⟨46,by decide⟩).lower ∧ (cell12958 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12958 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12958 ⟨47,by decide⟩).lower ∧ (cell12958 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12958 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12958 ⟨48,by decide⟩).lower ∧ (cell12958 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12958 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12958 ⟨49,by decide⟩).lower ∧ (cell12958 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12958 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12958 ⟨50,by decide⟩).lower ∧ (cell12958 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12958 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12958 ⟨51,by decide⟩).lower ∧ (cell12958 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12958 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12958 ⟨52,by decide⟩).lower ∧ (cell12958 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12958 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12958 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12958 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12958,cell12958,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12958 i).lower ∧
    (cell12958 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12958 i).upper ≤ (0.532 : ℝ) ∧
    (cell12958 i).centre ≤ (0.1 : ℝ) ∧ (cell12958 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12958 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12958 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12958

/-! The local source numeric instances at 12958 have no network premises. -/
namespace BstLean.Part269.N12958
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12958)
open BstLean.Part268 (cell12958)

noncomputable def sourceNumerics12958 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12958 (cell12958 i)
      scalarRow12958.M scalarRow12958.H scalarRow12958.xi := by
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
    energy_allowance := scalarRow12958.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12958]
    centre_nonneg := (scalarRow12958.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12958])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12958
/-! Actual 12959 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12959 ≤ (1.035446439889 : ℝ) := by
  have hr : (113.837603629029 : ℝ) ≤ √(12959 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.837603629029 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12959 12959 (11 / 1000) ≤
    (0.008396934978 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12959) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.837603629029 : ℝ) ≤ √(12959 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12959)
  have hdiv : K / √(12959 : ℝ) ≤ K / 113.837603629029 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.837603629029 ≤ (0.008396934978 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12959.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12959 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12959 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12959 := gPlus_lower 12959
end BstLean.Part269.N12959

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12959
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035446439888 : ℝ) ≤ wn 12959 := by
  have hn : √(12959 : ℝ) ≤ 113.837603629030 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12959 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.837603629030 ≤ 2 / √(12959 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246760295 : ℝ) ≤ rhoBar 12959 BstLean.Part154.csC ∧
    rhoBar 12959 BstLean.Part154.csC ≤ 0.000246760677 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035446439888 : ℝ) / (1.295212 * 12959) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035446439889 : ℝ) / (1.29521 * 12959) := by gcongr
      _ ≤ (0.000246760677 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12959 BstLean.Part154.csC) ≤ 0.000987103599 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12959 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) ≤ 0.000188477291 ∧
    cc1 (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) ≤ 0.000119929389 ∧
    cc2 (rhoBar 12959 BstLean.Part154.csC) ≤ 0.000069619974 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12959 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12959 BstLean.Part154.csC * nuR (rhoBar 12959 BstLean.Part154.csC)) ≤ 0.000493536577 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246760677 : ℝ) * 0.000987103599 := by gcongr
      _ ≤ (0.000493536577 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12959 BstLean.Part154.csC) * nuR (rhoBar 12959 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987103599 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12959 BstLean.Part154.csC) * rhoBar 12959 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246760677 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246760677 / 2 + 0.399 * 0.000987103599 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188477291 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493536577 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119929389 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246760677 / 1.414213562 := by gcongr
      _ ≤ (0.000069619974 : ℝ) := by norm_num

end BstLean.Part269.N12959

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12959
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) ≤ 1.53410E-7 := by
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12959 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12959 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188477291 : ℝ) ^ 2 + 0.000119929389 ^ 2 + 3 * 0.000069619974 ^ 2 +
        2 * 0.797885 * 0.000188477291 * 0.000119929389 + 2 * 0.000188477291 * 0.000069619974 +
        4 * 0.797885 * 0.000119929389 * 0.000069619974 := by gcongr
    _ ≤ (1.53410E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12959 BstLean.Part154.csC Θ ≤ 0.002574933514 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12959 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12959 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035446439889 * 1.53410E-7 / (0.000246760295 : ℝ) := by gcongr
    _ ≤ 0.002574933514 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12959 BstLean.Part154.csC Θ ≤ 0.002856025137 + 0.000650644551 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12959 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035446439889 : ℝ) * ((2 * Θ * 0.000246760677 +
        (6863 / 10000) * 0.000246760677 * 12959 * 0.000987103599) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002856025137 + 0.000650644551 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12959 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12959 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12959 0.011 Θ ∧ gammaRatio 12959 0.011 Θ ≤ 0.000084829940 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12959 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035446439889 : ℝ) * 0.525 / ((1 - 0.011) * 12959) := by gcongr
      _ ≤ (0.000084829940 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12959 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12959 0.011 Θ) :=
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
    badAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12959 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12959 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12959 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12959 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12959 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12959 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12959 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12959 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12959 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12959 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035446439889 : ℝ) * 12959 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003277381614 + 0.003225578065 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12959

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12959
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12959 BstLean.Part154.csC) (piBar (rhoBar 12959 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12959 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12959 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12959 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12959 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12959 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12959 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12959 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12959 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12959 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051951528620 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12959) ≤ 0.010490712586 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12959 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035446439889)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010490712586 + 2 * 0.737676 / 12959) := by gcongr
    _ ≤ (0.051951528620 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12959 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12959

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12959
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515046948 : ℝ) ≤ plow 12959 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12959) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477410099)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351840095) : eMP 12959 0.011 xi bn ≤ 0.001164150700 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12959 : ℝ) * (1 - 0.011))) ≤ 0.000575643668 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351840095 / (12959 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575643668 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575643668 : ℝ) + 3.141593 * 0.052477410099 / (12959 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164150700 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477410099)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351840095) : PiBarMP 12959 12 0.011 xi bn ≤ 0.159615338478 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12959 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036767378137 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.209765479838 : ℝ) ≤ √((12959 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.837603629029 : ℝ) ≤ √(12959 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12959) ≤ 0.122388453540 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036767378137 + 0.052477410099 * 1.772454 / (2 * (113.209765479838 : ℝ))) * (1 + 0.001164150700) +
        8 / (12959 * 113.837603629029) + 0.122388453540 := by gcongr
    _ ≤ (0.159615338478 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477410099)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351840095) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281031012859) :
    parallelOracle 12959 0.011 xi bn cd ≤ 0.160585717526 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12959 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12959 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515046948 : ℝ) ≤ plow 12959 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.837603629029 : ℝ) ≤ √(12959 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281031012859 : ℝ) / (2 * 0.560515046948 * 113.837603629029)) * 0.159615338478 +
        0.281031012859 ^ 2 / (2 * 0.560515046948 * 113.837603629029) := by gcongr
    _ ≤ (0.160585717526 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477410099) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351840095)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281031012859) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12959 12959 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515046948 : ℝ) ≤ plow 12959 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.837603629029 : ℝ) ≤ √(12959 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12959 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12959 Θ 1.22 ≤ 0.011649054950 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.837603629029 := by gcongr <;> linarith
      _ ≤ (0.011649054950 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12959 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12959 12959 0.011 ≤ 0.008396934978 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12959 12959 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12959 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12959 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12959 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12959 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160585717526 + 0.011649054950 + (0.008396934978 : ℝ) *
        (1 + 2 * (0.281031012859 + 0.011649054950) / (0.560515046948 * 113.837603629029))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12959]

end BstLean.Part269.N12959

/-! The original eight local profiles supply actual 12959 moment certificates. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12959 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052477410099 ∧
    0 ≤ bN 12959 BstLean.Part154.csC (groupTheta g) ∧ bN 12959 BstLean.Part154.csC (groupTheta g) ≤ 0.001351840095 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12959 12959 0.011
      (momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12959 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12959 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12959 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229079484239 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12959 0.011
      (momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12959 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12959
/-! The actual computed-centre upper energy formula at 12959. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12959

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12959)
open BstLean.Part268 (cell12959)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084768360886
  | 2 => 0.085698572100
  | 3 => 0.086625213412
  | 4 => 0.087549301262
  | 5 => 0.088472077016
  | 6 => 0.089395041870
  | 7 => 0.090319995318
  | 8 => 0.091249077269
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12959 12959 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12959 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12959

/-! Actual upper energy certificates on all 43 source endpoints at 12959. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12959)
open BstLean.Part268 (cell12959)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12959 (gMinus 12959) (1 - (cell12959 i).lower) ≤ 1 ∧
    energyUpper 12959 (gMinus 12959) (BstLean.Part211.gPlus 12959)
      (finiteEnergy 12959 12959 0.011) (1 - (cell12959 i).lower) ≤
      (cell12959 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨10,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨11,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨12,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨13,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨14,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨15,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨16,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨17,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨18,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨19,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨20,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨21,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨22,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨23,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨24,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨25,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨26,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨27,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨28,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨29,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨30,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨31,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨32,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨33,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨34,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨35,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨36,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨37,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨38,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨39,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨40,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨41,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨42,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨43,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨44,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨45,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨46,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨47,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨48,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨49,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨50,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨51,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12959) (by norm_num)
        (q := 1 - (cell12959 ⟨52,by decide⟩).lower)
        (by norm_num [cell12959]) (by norm_num [cell12959])
      exact ⟨E.1,E.2.trans (by norm_num [cell12959])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12959

/-! Source-cell containment and simple scalar guards at 12959. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12959)
open BstLean.Part268 (cell12959)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12959 ⟨10,by decide⟩).lower ∧ (cell12959 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12959 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12959 ⟨11,by decide⟩).lower ∧ (cell12959 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12959 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12959 ⟨12,by decide⟩).lower ∧ (cell12959 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12959 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12959 ⟨13,by decide⟩).lower ∧ (cell12959 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12959 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12959 ⟨14,by decide⟩).lower ∧ (cell12959 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12959 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12959 ⟨15,by decide⟩).lower ∧ (cell12959 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12959 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12959 ⟨16,by decide⟩).lower ∧ (cell12959 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12959 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12959 ⟨17,by decide⟩).lower ∧ (cell12959 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12959 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12959 ⟨18,by decide⟩).lower ∧ (cell12959 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12959 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12959 ⟨19,by decide⟩).lower ∧ (cell12959 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12959 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12959 ⟨20,by decide⟩).lower ∧ (cell12959 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12959 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12959 ⟨21,by decide⟩).lower ∧ (cell12959 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12959 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12959 ⟨22,by decide⟩).lower ∧ (cell12959 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12959 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12959 ⟨23,by decide⟩).lower ∧ (cell12959 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12959 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12959 ⟨24,by decide⟩).lower ∧ (cell12959 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12959 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12959 ⟨25,by decide⟩).lower ∧ (cell12959 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12959 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12959 ⟨26,by decide⟩).lower ∧ (cell12959 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12959 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12959 ⟨27,by decide⟩).lower ∧ (cell12959 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12959 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12959 ⟨28,by decide⟩).lower ∧ (cell12959 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12959 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12959 ⟨29,by decide⟩).lower ∧ (cell12959 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12959 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12959 ⟨30,by decide⟩).lower ∧ (cell12959 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12959 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12959 ⟨31,by decide⟩).lower ∧ (cell12959 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12959 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12959 ⟨32,by decide⟩).lower ∧ (cell12959 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12959 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12959 ⟨33,by decide⟩).lower ∧ (cell12959 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12959 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12959 ⟨34,by decide⟩).lower ∧ (cell12959 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12959 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12959 ⟨35,by decide⟩).lower ∧ (cell12959 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12959 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12959 ⟨36,by decide⟩).lower ∧ (cell12959 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12959 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12959 ⟨37,by decide⟩).lower ∧ (cell12959 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12959 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12959 ⟨38,by decide⟩).lower ∧ (cell12959 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12959 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12959 ⟨39,by decide⟩).lower ∧ (cell12959 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12959 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12959 ⟨40,by decide⟩).lower ∧ (cell12959 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12959 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12959 ⟨41,by decide⟩).lower ∧ (cell12959 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12959 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12959 ⟨42,by decide⟩).lower ∧ (cell12959 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12959 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12959 ⟨43,by decide⟩).lower ∧ (cell12959 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12959 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12959 ⟨44,by decide⟩).lower ∧ (cell12959 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12959 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12959 ⟨45,by decide⟩).lower ∧ (cell12959 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12959 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12959 ⟨46,by decide⟩).lower ∧ (cell12959 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12959 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12959 ⟨47,by decide⟩).lower ∧ (cell12959 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12959 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12959 ⟨48,by decide⟩).lower ∧ (cell12959 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12959 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12959 ⟨49,by decide⟩).lower ∧ (cell12959 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12959 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12959 ⟨50,by decide⟩).lower ∧ (cell12959 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12959 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12959 ⟨51,by decide⟩).lower ∧ (cell12959 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12959 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12959 ⟨52,by decide⟩).lower ∧ (cell12959 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12959 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12959 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12959 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12959,cell12959,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12959 i).lower ∧
    (cell12959 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12959 i).upper ≤ (0.532 : ℝ) ∧
    (cell12959 i).centre ≤ (0.1 : ℝ) ∧ (cell12959 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12959 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12959 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12959

/-! The local source numeric instances at 12959 have no network premises. -/
namespace BstLean.Part269.N12959
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12959)
open BstLean.Part268 (cell12959)

noncomputable def sourceNumerics12959 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12959 (cell12959 i)
      scalarRow12959.M scalarRow12959.H scalarRow12959.xi := by
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
    energy_allowance := scalarRow12959.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12959]
    centre_nonneg := (scalarRow12959.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12959])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12959
/-! Actual 12960 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12960 ≤ (1.035445060422 : ℝ) := by
  have hr : (113.841995766061 : ℝ) ≤ √(12960 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.841995766061 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12960 12960 (11 / 1000) ≤
    (0.008396611013 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12960) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.841995766061 : ℝ) ≤ √(12960 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12960)
  have hdiv : K / √(12960 : ℝ) ≤ K / 113.841995766061 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.841995766061 ≤ (0.008396611013 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12960.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12960 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12960 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12960 := gPlus_lower 12960
end BstLean.Part269.N12960

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12960
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035445060421 : ℝ) ≤ wn 12960 := by
  have hn : √(12960 : ℝ) ≤ 113.841995766062 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12960 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.841995766062 ≤ 2 / √(12960 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246740926 : ℝ) ≤ rhoBar 12960 BstLean.Part154.csC ∧
    rhoBar 12960 BstLean.Part154.csC ≤ 0.000246741308 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035445060421 : ℝ) / (1.295212 * 12960) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035445060422 : ℝ) / (1.29521 * 12960) := by gcongr
      _ ≤ (0.000246741308 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12960 BstLean.Part154.csC) ≤ 0.000987026114 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12960 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) ≤ 0.000188462497 ∧
    cc1 (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) ≤ 0.000119919975 ∧
    cc2 (rhoBar 12960 BstLean.Part154.csC) ≤ 0.000069614509 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12960 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12960 BstLean.Part154.csC * nuR (rhoBar 12960 BstLean.Part154.csC)) ≤ 0.000493497837 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246741308 : ℝ) * 0.000987026114 := by gcongr
      _ ≤ (0.000493497837 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12960 BstLean.Part154.csC) * nuR (rhoBar 12960 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000987026114 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12960 BstLean.Part154.csC) * rhoBar 12960 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246741308 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246741308 / 2 + 0.399 * 0.000987026114 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188462497 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493497837 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119919975 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246741308 / 1.414213562 := by gcongr
      _ ≤ (0.000069614509 : ℝ) := by norm_num

end BstLean.Part269.N12960

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12960
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) ≤ 1.53386E-7 := by
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12960 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12960 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188462497 : ℝ) ^ 2 + 0.000119919975 ^ 2 + 3 * 0.000069614509 ^ 2 +
        2 * 0.797885 * 0.000188462497 * 0.000119919975 + 2 * 0.000188462497 * 0.000069614509 +
        4 * 0.797885 * 0.000119919975 * 0.000069614509 := by gcongr
    _ ≤ (1.53386E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12960 BstLean.Part154.csC Θ ≤ 0.002574729351 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12960 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12960 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035445060422 * 1.53386E-7 / (0.000246740926 : ℝ) := by gcongr
    _ ≤ 0.002574729351 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12960 BstLean.Part154.csC Θ ≤ 0.002855793336 + 0.000650592614 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12960 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035445060422 : ℝ) * ((2 * Θ * 0.000246741308 +
        (6863 / 10000) * 0.000246741308 * 12960 * 0.000987026114) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002855793336 + 0.000650592614 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12960 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12960 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12960 0.011 Θ ∧ gammaRatio 12960 0.011 Θ ≤ 0.000084823281 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12960 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035445060422 : ℝ) * 0.525 / ((1 - 0.011) * 12960) := by gcongr
      _ ≤ (0.000084823281 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12960 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12960 0.011 Θ) :=
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
    badAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12960 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12960 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12960 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12960 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12960 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12960 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12960 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12960 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12960 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12960 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035445060422 : ℝ) * 12960 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003277149813 + 0.003225321965 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12960

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12960
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12960 BstLean.Part154.csC) (piBar (rhoBar 12960 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12960 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12960 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12960 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12960 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12960 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12960 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12960 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12960 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12960 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051949502762 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12960) ≤ 0.010490307844 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12960 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035445060422)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010490307844 + 2 * 0.737676 / 12960) := by gcongr
    _ ≤ (0.051949502762 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12960 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12960

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12960
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515090378 : ℝ) ≤ plow 12960 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12960) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477043845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351732910) : eMP 12960 0.011 xi bn ≤ 0.001164059557 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12960 : ℝ) * (1 - 0.011))) ≤ 0.000575598638 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351732910 / (12960 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575598638 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575598638 : ℝ) + 3.141593 * 0.052477043845 / (12960 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001164059557 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477043845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351732910) : PiBarMP 12960 12 0.011 xi bn ≤ 0.159609134520 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12960 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036765920498 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.214133393317 : ℝ) ≤ √((12960 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.841995766061 : ℝ) ≤ √(12960 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12960) ≤ 0.122383731672 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036765920498 + 0.052477043845 * 1.772454 / (2 * (113.214133393317 : ℝ))) * (1 + 0.001164059557) +
        8 / (12960 * 113.841995766061) + 0.122383731672 := by gcongr
    _ ≤ (0.159609134520 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477043845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351732910) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281028187596) :
    parallelOracle 12960 0.011 xi bn cd ≤ 0.160579446417 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12960 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12960 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515090378 : ℝ) ≤ plow 12960 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.841995766061 : ℝ) ≤ √(12960 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281028187596 : ℝ) / (2 * 0.560515090378 * 113.841995766061)) * 0.159609134520 +
        0.281028187596 ^ 2 / (2 * 0.560515090378 * 113.841995766061) := by gcongr
    _ ≤ (0.160579446417 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052477043845) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351732910)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281028187596) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12960 12960 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515090378 : ℝ) ≤ plow 12960 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.841995766061 : ℝ) ≤ √(12960 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12960 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12960 Θ 1.22 ≤ 0.011648605518 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.841995766061 := by gcongr <;> linarith
      _ ≤ (0.011648605518 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12960 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12960 12960 0.011 ≤ 0.008396611013 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12960 12960 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12960 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12960 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12960 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12960 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160579446417 + 0.011648605518 + (0.008396611013 : ℝ) *
        (1 + 2 * (0.281028187596 + 0.011648605518) / (0.560515090378 * 113.841995766061))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12960]

end BstLean.Part269.N12960

/-! The original eight local profiles supply actual 12960 moment certificates. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12960 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052477043845 ∧
    0 ≤ bN 12960 BstLean.Part154.csC (groupTheta g) ∧ bN 12960 BstLean.Part154.csC (groupTheta g) ≤ 0.001351732910 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12960 12960 0.011
      (momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12960 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12960 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12960 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229078684834 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12960 0.011
      (momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12960 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12960
/-! The actual computed-centre upper energy formula at 12960. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12960

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12960)
open BstLean.Part268 (cell12960)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084765692698
  | 2 => 0.085695860144
  | 3 => 0.086622452181
  | 4 => 0.087546483922
  | 5 => 0.088469195169
  | 6 => 0.089392085276
  | 7 => 0.090316951584
  | 8 => 0.091245931509
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12960 12960 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12960 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12960

/-! Actual upper energy certificates on all 43 source endpoints at 12960. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12960)
open BstLean.Part268 (cell12960)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12960 (gMinus 12960) (1 - (cell12960 i).lower) ≤ 1 ∧
    energyUpper 12960 (gMinus 12960) (BstLean.Part211.gPlus 12960)
      (finiteEnergy 12960 12960 0.011) (1 - (cell12960 i).lower) ≤
      (cell12960 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨10,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨11,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨12,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨13,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨14,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨15,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨16,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨17,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨18,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨19,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨20,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨21,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨22,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨23,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨24,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨25,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨26,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨27,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨28,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨29,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨30,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨31,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨32,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨33,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨34,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨35,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨36,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨37,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨38,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨39,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨40,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨41,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨42,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨43,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨44,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨45,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨46,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨47,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨48,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨49,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨50,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨51,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12960) (by norm_num)
        (q := 1 - (cell12960 ⟨52,by decide⟩).lower)
        (by norm_num [cell12960]) (by norm_num [cell12960])
      exact ⟨E.1,E.2.trans (by norm_num [cell12960])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12960

/-! Source-cell containment and simple scalar guards at 12960. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12960)
open BstLean.Part268 (cell12960)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12960 ⟨10,by decide⟩).lower ∧ (cell12960 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12960 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12960 ⟨11,by decide⟩).lower ∧ (cell12960 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12960 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12960 ⟨12,by decide⟩).lower ∧ (cell12960 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12960 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12960 ⟨13,by decide⟩).lower ∧ (cell12960 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12960 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12960 ⟨14,by decide⟩).lower ∧ (cell12960 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12960 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12960 ⟨15,by decide⟩).lower ∧ (cell12960 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12960 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12960 ⟨16,by decide⟩).lower ∧ (cell12960 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12960 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12960 ⟨17,by decide⟩).lower ∧ (cell12960 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12960 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12960 ⟨18,by decide⟩).lower ∧ (cell12960 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12960 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12960 ⟨19,by decide⟩).lower ∧ (cell12960 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12960 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12960 ⟨20,by decide⟩).lower ∧ (cell12960 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12960 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12960 ⟨21,by decide⟩).lower ∧ (cell12960 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12960 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12960 ⟨22,by decide⟩).lower ∧ (cell12960 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12960 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12960 ⟨23,by decide⟩).lower ∧ (cell12960 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12960 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12960 ⟨24,by decide⟩).lower ∧ (cell12960 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12960 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12960 ⟨25,by decide⟩).lower ∧ (cell12960 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12960 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12960 ⟨26,by decide⟩).lower ∧ (cell12960 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12960 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12960 ⟨27,by decide⟩).lower ∧ (cell12960 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12960 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12960 ⟨28,by decide⟩).lower ∧ (cell12960 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12960 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12960 ⟨29,by decide⟩).lower ∧ (cell12960 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12960 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12960 ⟨30,by decide⟩).lower ∧ (cell12960 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12960 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12960 ⟨31,by decide⟩).lower ∧ (cell12960 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12960 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12960 ⟨32,by decide⟩).lower ∧ (cell12960 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12960 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12960 ⟨33,by decide⟩).lower ∧ (cell12960 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12960 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12960 ⟨34,by decide⟩).lower ∧ (cell12960 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12960 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12960 ⟨35,by decide⟩).lower ∧ (cell12960 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12960 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12960 ⟨36,by decide⟩).lower ∧ (cell12960 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12960 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12960 ⟨37,by decide⟩).lower ∧ (cell12960 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12960 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12960 ⟨38,by decide⟩).lower ∧ (cell12960 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12960 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12960 ⟨39,by decide⟩).lower ∧ (cell12960 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12960 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12960 ⟨40,by decide⟩).lower ∧ (cell12960 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12960 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12960 ⟨41,by decide⟩).lower ∧ (cell12960 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12960 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12960 ⟨42,by decide⟩).lower ∧ (cell12960 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12960 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12960 ⟨43,by decide⟩).lower ∧ (cell12960 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12960 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12960 ⟨44,by decide⟩).lower ∧ (cell12960 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12960 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12960 ⟨45,by decide⟩).lower ∧ (cell12960 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12960 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12960 ⟨46,by decide⟩).lower ∧ (cell12960 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12960 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12960 ⟨47,by decide⟩).lower ∧ (cell12960 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12960 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12960 ⟨48,by decide⟩).lower ∧ (cell12960 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12960 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12960 ⟨49,by decide⟩).lower ∧ (cell12960 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12960 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12960 ⟨50,by decide⟩).lower ∧ (cell12960 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12960 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12960 ⟨51,by decide⟩).lower ∧ (cell12960 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12960 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12960 ⟨52,by decide⟩).lower ∧ (cell12960 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12960 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12960 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12960 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12960,cell12960,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12960 i).lower ∧
    (cell12960 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12960 i).upper ≤ (0.532 : ℝ) ∧
    (cell12960 i).centre ≤ (0.1 : ℝ) ∧ (cell12960 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12960 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12960 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12960

/-! The local source numeric instances at 12960 have no network premises. -/
namespace BstLean.Part269.N12960
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12960)
open BstLean.Part268 (cell12960)

noncomputable def sourceNumerics12960 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12960 (cell12960 i)
      scalarRow12960.M scalarRow12960.H scalarRow12960.xi := by
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
    energy_allowance := scalarRow12960.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12960]
    centre_nonneg := (scalarRow12960.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12960])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12960
/-! Actual 12961 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12961 ≤ (1.035443681116 : ℝ) := by
  have hr : (113.846387733647 : ℝ) ≤ √(12961 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.846387733647 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12961 12961 (11 / 1000) ≤
    (0.008396287086 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12961) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.846387733647 : ℝ) ≤ √(12961 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12961)
  have hdiv : K / √(12961 : ℝ) ≤ K / 113.846387733647 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.846387733647 ≤ (0.008396287086 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12961.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12961 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12961 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12961 := gPlus_lower 12961
end BstLean.Part269.N12961

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12961
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035443681115 : ℝ) ≤ wn 12961 := by
  have hn : √(12961 : ℝ) ≤ 113.846387733648 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12961 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.846387733648 ≤ 2 / √(12961 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246721560 : ℝ) ≤ rhoBar 12961 BstLean.Part154.csC ∧
    rhoBar 12961 BstLean.Part154.csC ≤ 0.000246721942 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035443681115 : ℝ) / (1.295212 * 12961) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035443681116 : ℝ) / (1.29521 * 12961) := by gcongr
      _ ≤ (0.000246721942 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12961 BstLean.Part154.csC) ≤ 0.000986948640 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12961 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) ≤ 0.000188447704 ∧
    cc1 (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) ≤ 0.000119910562 ∧
    cc2 (rhoBar 12961 BstLean.Part154.csC) ≤ 0.000069609045 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12961 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12961 BstLean.Part154.csC * nuR (rhoBar 12961 BstLean.Part154.csC)) ≤ 0.000493459102 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246721942 : ℝ) * 0.000986948640 := by gcongr
      _ ≤ (0.000493459102 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12961 BstLean.Part154.csC) * nuR (rhoBar 12961 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986948640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12961 BstLean.Part154.csC) * rhoBar 12961 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246721942 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246721942 / 2 + 0.399 * 0.000986948640 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188447704 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493459102 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119910562 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246721942 / 1.414213562 := by gcongr
      _ ≤ (0.000069609045 : ℝ) := by norm_num

end BstLean.Part269.N12961

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12961
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) ≤ 1.53362E-7 := by
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12961 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12961 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188447704 : ℝ) ^ 2 + 0.000119910562 ^ 2 + 3 * 0.000069609045 ^ 2 +
        2 * 0.797885 * 0.000188447704 * 0.000119910562 + 2 * 0.000188447704 * 0.000069609045 +
        4 * 0.797885 * 0.000119910562 * 0.000069609045 := by gcongr
    _ ≤ (1.53362E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12961 BstLean.Part154.csC Θ ≤ 0.002574525126 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12961 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12961 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035443681116 * 1.53362E-7 / (0.000246721560 : ℝ) := by gcongr
    _ ≤ 0.002574525126 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12961 BstLean.Part154.csC Θ ≤ 0.002855561569 + 0.000650540684 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12961 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035443681116 : ℝ) * ((2 * Θ * 0.000246721942 +
        (6863 / 10000) * 0.000246721942 * 12961 * 0.000986948640) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002855561569 + 0.000650540684 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12961 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12961 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12961 0.011 Θ ∧ gammaRatio 12961 0.011 Θ ≤ 0.000084816624 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12961 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035443681116 : ℝ) * 0.525 / ((1 - 0.011) * 12961) := by gcongr
      _ ≤ (0.000084816624 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12961 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12961 0.011 Θ) :=
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
    badAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12961 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12961 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12961 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12961 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12961 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12961 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12961 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12961 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12961 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12961 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035443681116 : ℝ) * 12961 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003276918046 + 0.003225065810 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12961

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12961
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12961 BstLean.Part154.csC) (piBar (rhoBar 12961 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12961 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12961 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12961 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12961 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12961 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12961 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12961 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12961 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12961 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051947477136 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12961) ≤ 0.010489903148 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12961 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035443681116)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010489903148 + 2 * 0.737676 / 12961) := by gcongr
    _ ≤ (0.051947477136 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12961 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12961

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12961
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515133801 : ℝ) ≤ plow 12961 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12961) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476677597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351625692) : eMP 12961 0.011 xi bn ≤ 0.001163968409 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12961 : ℝ) * (1 - 0.011))) ≤ 0.000575553605 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351625692 / (12961 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575553605 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575553605 : ℝ) + 3.141593 * 0.052476677597 / (12961 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163968409 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476677597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351625692) : PiBarMP 12961 12 0.011 xi bn ≤ 0.159602930602 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12961 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036764462352 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.218501138285 : ℝ) ≤ √((12961 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.846387733647 : ℝ) ≤ √(12961 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12961) ≤ 0.122379010350 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036764462352 + 0.052476677597 * 1.772454 / (2 * (113.218501138285 : ℝ))) * (1 + 0.001163968409) +
        8 / (12961 * 113.846387733647) + 0.122379010350 := by gcongr
    _ ≤ (0.159602930602 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476677597)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351625692) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281025362575) :
    parallelOracle 12961 0.011 xi bn cd ≤ 0.160573175356 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12961 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12961 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515133801 : ℝ) ≤ plow 12961 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.846387733647 : ℝ) ≤ √(12961 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281025362575 : ℝ) / (2 * 0.560515133801 * 113.846387733647)) * 0.159602930602 +
        0.281025362575 ^ 2 / (2 * 0.560515133801 * 113.846387733647) := by gcongr
    _ ≤ (0.160573175356 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476677597) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351625692)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281025362575) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12961 12961 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515133801 : ℝ) ≤ plow 12961 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.846387733647 : ℝ) ≤ √(12961 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12961 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12961 Θ 1.22 ≤ 0.011648156138 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.846387733647 := by gcongr <;> linarith
      _ ≤ (0.011648156138 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12961 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12961 12961 0.011 ≤ 0.008396287086 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12961 12961 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12961 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12961 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12961 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12961 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160573175356 + 0.011648156138 + (0.008396287086 : ℝ) *
        (1 + 2 * (0.281025362575 + 0.011648156138) / (0.560515133801 * 113.846387733647))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12961]

end BstLean.Part269.N12961

/-! The original eight local profiles supply actual 12961 moment certificates. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12961 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052476677597 ∧
    0 ≤ bN 12961 BstLean.Part154.csC (groupTheta g) ∧ bN 12961 BstLean.Part154.csC (groupTheta g) ≤ 0.001351625692 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12961 12961 0.011
      (momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12961 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12961 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12961 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229077885439 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12961 0.011
      (momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12961 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12961
/-! The actual computed-centre upper energy formula at 12961. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12961

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12961)
open BstLean.Part268 (cell12961)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084763025351
  | 2 => 0.085693149062
  | 3 => 0.086619691862
  | 4 => 0.087543667543
  | 5 => 0.088466314342
  | 6 => 0.089389129773
  | 7 => 0.090313909031
  | 8 => 0.091242787036
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12961 12961 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12961 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12961

/-! Actual upper energy certificates on all 43 source endpoints at 12961. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12961)
open BstLean.Part268 (cell12961)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12961 (gMinus 12961) (1 - (cell12961 i).lower) ≤ 1 ∧
    energyUpper 12961 (gMinus 12961) (BstLean.Part211.gPlus 12961)
      (finiteEnergy 12961 12961 0.011) (1 - (cell12961 i).lower) ≤
      (cell12961 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨10,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨11,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨12,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨13,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨14,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨15,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨16,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨17,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨18,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨19,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨20,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨21,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨22,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨23,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨24,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨25,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨26,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨27,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨28,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨29,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨30,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨31,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨32,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨33,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨34,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨35,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨36,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨37,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨38,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨39,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨40,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨41,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨42,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨43,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨44,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨45,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨46,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨47,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨48,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨49,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨50,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨51,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12961) (by norm_num)
        (q := 1 - (cell12961 ⟨52,by decide⟩).lower)
        (by norm_num [cell12961]) (by norm_num [cell12961])
      exact ⟨E.1,E.2.trans (by norm_num [cell12961])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12961

/-! Source-cell containment and simple scalar guards at 12961. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12961)
open BstLean.Part268 (cell12961)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12961 ⟨10,by decide⟩).lower ∧ (cell12961 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12961 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12961 ⟨11,by decide⟩).lower ∧ (cell12961 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12961 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12961 ⟨12,by decide⟩).lower ∧ (cell12961 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12961 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12961 ⟨13,by decide⟩).lower ∧ (cell12961 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12961 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12961 ⟨14,by decide⟩).lower ∧ (cell12961 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12961 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12961 ⟨15,by decide⟩).lower ∧ (cell12961 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12961 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12961 ⟨16,by decide⟩).lower ∧ (cell12961 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12961 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12961 ⟨17,by decide⟩).lower ∧ (cell12961 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12961 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12961 ⟨18,by decide⟩).lower ∧ (cell12961 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12961 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12961 ⟨19,by decide⟩).lower ∧ (cell12961 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12961 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12961 ⟨20,by decide⟩).lower ∧ (cell12961 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12961 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12961 ⟨21,by decide⟩).lower ∧ (cell12961 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12961 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12961 ⟨22,by decide⟩).lower ∧ (cell12961 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12961 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12961 ⟨23,by decide⟩).lower ∧ (cell12961 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12961 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12961 ⟨24,by decide⟩).lower ∧ (cell12961 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12961 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12961 ⟨25,by decide⟩).lower ∧ (cell12961 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12961 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12961 ⟨26,by decide⟩).lower ∧ (cell12961 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12961 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12961 ⟨27,by decide⟩).lower ∧ (cell12961 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12961 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12961 ⟨28,by decide⟩).lower ∧ (cell12961 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12961 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12961 ⟨29,by decide⟩).lower ∧ (cell12961 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12961 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12961 ⟨30,by decide⟩).lower ∧ (cell12961 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12961 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12961 ⟨31,by decide⟩).lower ∧ (cell12961 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12961 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12961 ⟨32,by decide⟩).lower ∧ (cell12961 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12961 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12961 ⟨33,by decide⟩).lower ∧ (cell12961 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12961 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12961 ⟨34,by decide⟩).lower ∧ (cell12961 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12961 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12961 ⟨35,by decide⟩).lower ∧ (cell12961 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12961 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12961 ⟨36,by decide⟩).lower ∧ (cell12961 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12961 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12961 ⟨37,by decide⟩).lower ∧ (cell12961 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12961 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12961 ⟨38,by decide⟩).lower ∧ (cell12961 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12961 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12961 ⟨39,by decide⟩).lower ∧ (cell12961 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12961 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12961 ⟨40,by decide⟩).lower ∧ (cell12961 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12961 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12961 ⟨41,by decide⟩).lower ∧ (cell12961 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12961 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12961 ⟨42,by decide⟩).lower ∧ (cell12961 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12961 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12961 ⟨43,by decide⟩).lower ∧ (cell12961 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12961 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12961 ⟨44,by decide⟩).lower ∧ (cell12961 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12961 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12961 ⟨45,by decide⟩).lower ∧ (cell12961 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12961 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12961 ⟨46,by decide⟩).lower ∧ (cell12961 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12961 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12961 ⟨47,by decide⟩).lower ∧ (cell12961 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12961 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12961 ⟨48,by decide⟩).lower ∧ (cell12961 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12961 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12961 ⟨49,by decide⟩).lower ∧ (cell12961 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12961 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12961 ⟨50,by decide⟩).lower ∧ (cell12961 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12961 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12961 ⟨51,by decide⟩).lower ∧ (cell12961 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12961 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12961 ⟨52,by decide⟩).lower ∧ (cell12961 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12961 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12961 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12961 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12961,cell12961,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12961 i).lower ∧
    (cell12961 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12961 i).upper ≤ (0.532 : ℝ) ∧
    (cell12961 i).centre ≤ (0.1 : ℝ) ∧ (cell12961 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12961 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12961 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12961

/-! The local source numeric instances at 12961 have no network premises. -/
namespace BstLean.Part269.N12961
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12961)
open BstLean.Part268 (cell12961)

noncomputable def sourceNumerics12961 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12961 (cell12961 i)
      scalarRow12961.M scalarRow12961.H scalarRow12961.xi := by
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
    energy_allowance := scalarRow12961.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12961]
    centre_nonneg := (scalarRow12961.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12961])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12961
/-! Actual 12962 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12962 ≤ (1.035442301970 : ℝ) := by
  have hr : (113.850779531806 : ℝ) ≤ √(12962 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.850779531806 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12962 12962 (11 / 1000) ≤
    (0.008395963196 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12962) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.850779531806 : ℝ) ≤ √(12962 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12962)
  have hdiv : K / √(12962 : ℝ) ≤ K / 113.850779531806 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.850779531806 ≤ (0.008395963196 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12962.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12962 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12962 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12962 := gPlus_lower 12962
end BstLean.Part269.N12962

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12962
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035442301969 : ℝ) ≤ wn 12962 := by
  have hn : √(12962 : ℝ) ≤ 113.850779531807 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12962 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.850779531807 ≤ 2 / √(12962 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246702197 : ℝ) ≤ rhoBar 12962 BstLean.Part154.csC ∧
    rhoBar 12962 BstLean.Part154.csC ≤ 0.000246702579 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035442301969 : ℝ) / (1.295212 * 12962) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035442301970 : ℝ) / (1.29521 * 12962) := by gcongr
      _ ≤ (0.000246702579 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12962 BstLean.Part154.csC) ≤ 0.000986871179 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12962 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) ≤ 0.000188432914 ∧
    cc1 (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) ≤ 0.000119901151 ∧
    cc2 (rhoBar 12962 BstLean.Part154.csC) ≤ 0.000069603582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12962 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12962 BstLean.Part154.csC * nuR (rhoBar 12962 BstLean.Part154.csC)) ≤ 0.000493420374 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246702579 : ℝ) * 0.000986871179 := by gcongr
      _ ≤ (0.000493420374 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12962 BstLean.Part154.csC) * nuR (rhoBar 12962 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986871179 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12962 BstLean.Part154.csC) * rhoBar 12962 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246702579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246702579 / 2 + 0.399 * 0.000986871179 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188432914 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493420374 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119901151 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246702579 / 1.414213562 := by gcongr
      _ ≤ (0.000069603582 : ℝ) := by norm_num

end BstLean.Part269.N12962

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12962
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) ≤ 1.53338E-7 := by
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12962 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12962 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188432914 : ℝ) ^ 2 + 0.000119901151 ^ 2 + 3 * 0.000069603582 ^ 2 +
        2 * 0.797885 * 0.000188432914 * 0.000119901151 + 2 * 0.000188432914 * 0.000069603582 +
        4 * 0.797885 * 0.000119901151 * 0.000069603582 := by gcongr
    _ ≤ (1.53338E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12962 BstLean.Part154.csC Θ ≤ 0.002574320840 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12962 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12962 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035442301970 * 1.53338E-7 / (0.000246702197 : ℝ) := by gcongr
    _ ≤ 0.002574320840 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12962 BstLean.Part154.csC Θ ≤ 0.002855329841 + 0.000650488762 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12962 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035442301970 : ℝ) * ((2 * Θ * 0.000246702579 +
        (6863 / 10000) * 0.000246702579 * 12962 * 0.000986871179) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002855329841 + 0.000650488762 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12962 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12962 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12962 0.011 Θ ∧ gammaRatio 12962 0.011 Θ ≤ 0.000084809967 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12962 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035442301970 : ℝ) * 0.525 / ((1 - 0.011) * 12962) := by gcongr
      _ ≤ (0.000084809967 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12962 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12962 0.011 Θ) :=
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
    badAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12962 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12962 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12962 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12962 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12962 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12962 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12962 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12962 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12962 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12962 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035442301970 : ℝ) * 12962 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003276686318 + 0.003224809602 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12962

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12962
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12962 BstLean.Part154.csC) (piBar (rhoBar 12962 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12962 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12962 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12962 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12962 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12962 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12962 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12962 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12962 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12962 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051945451751 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12962) ≤ 0.010489498500 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12962 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035442301970)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010489498500 + 2 * 0.737676 / 12962) := by gcongr
    _ ≤ (0.051945451751 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12962 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12962

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12962
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515177218 : ℝ) ≤ plow 12962 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12962) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476311360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351518441) : eMP 12962 0.011 xi bn ≤ 0.001163877255 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12962 : ℝ) * (1 - 0.011))) ≤ 0.000575508569 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351518441 / (12962 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575508569 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575508569 : ℝ) + 3.141593 * 0.052476311360 / (12962 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163877255 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476311360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351518441) : PiBarMP 12962 12 0.011 xi bn ≤ 0.159596726728 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12962 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036763003700 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.222868714760 : ℝ) ≤ √((12962 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.850779531806 : ℝ) ≤ √(12962 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12962) ≤ 0.122374289575 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036763003700 + 0.052476311360 * 1.772454 / (2 * (113.222868714760 : ℝ))) * (1 + 0.001163877255) +
        8 / (12962 * 113.850779531806) + 0.122374289575 := by gcongr
    _ ≤ (0.159596726728 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476311360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351518441) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281022537816) :
    parallelOracle 12962 0.011 xi bn cd ≤ 0.160566904348 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12962 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12962 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515177218 : ℝ) ≤ plow 12962 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.850779531806 : ℝ) ≤ √(12962 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281022537816 : ℝ) / (2 * 0.560515177218 * 113.850779531806)) * 0.159596726728 +
        0.281022537816 ^ 2 / (2 * 0.560515177218 * 113.850779531806) := by gcongr
    _ ≤ (0.160566904348 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052476311360) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351518441)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281022537816) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12962 12962 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515177218 : ℝ) ≤ plow 12962 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.850779531806 : ℝ) ≤ √(12962 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12962 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12962 Θ 1.22 ≤ 0.011647706810 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.850779531806 := by gcongr <;> linarith
      _ ≤ (0.011647706810 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12962 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12962 12962 0.011 ≤ 0.008395963196 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12962 12962 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12962 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12962 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12962 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12962 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160566904348 + 0.011647706810 + (0.008395963196 : ℝ) *
        (1 + 2 * (0.281022537816 + 0.011647706810) / (0.560515177218 * 113.850779531806))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12962]

end BstLean.Part269.N12962

/-! The original eight local profiles supply actual 12962 moment certificates. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12962 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052476311360 ∧
    0 ≤ bN 12962 BstLean.Part154.csC (groupTheta g) ∧ bN 12962 BstLean.Part154.csC (groupTheta g) ≤ 0.001351518441 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12962 12962 0.011
      (momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12962 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12962 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12962 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229077086065 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12962 0.011
      (momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12962 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12962
/-! The actual computed-centre upper energy formula at 12962. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12962

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12962)
open BstLean.Part268 (cell12962)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084760358845
  | 2 => 0.085690438852
  | 3 => 0.086616932455
  | 4 => 0.087540852124
  | 5 => 0.088463434534
  | 6 => 0.089386175362
  | 7 => 0.090310867656
  | 8 => 0.091239643847
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12962 12962 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12962 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12962

/-! Actual upper energy certificates on all 43 source endpoints at 12962. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12962)
open BstLean.Part268 (cell12962)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12962 (gMinus 12962) (1 - (cell12962 i).lower) ≤ 1 ∧
    energyUpper 12962 (gMinus 12962) (BstLean.Part211.gPlus 12962)
      (finiteEnergy 12962 12962 0.011) (1 - (cell12962 i).lower) ≤
      (cell12962 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨10,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨11,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨12,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨13,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨14,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨15,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨16,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨17,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨18,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨19,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨20,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨21,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨22,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨23,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨24,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨25,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨26,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨27,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨28,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨29,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨30,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨31,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨32,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨33,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨34,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨35,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨36,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨37,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨38,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨39,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨40,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨41,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨42,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨43,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨44,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨45,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨46,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨47,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨48,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨49,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨50,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨51,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12962) (by norm_num)
        (q := 1 - (cell12962 ⟨52,by decide⟩).lower)
        (by norm_num [cell12962]) (by norm_num [cell12962])
      exact ⟨E.1,E.2.trans (by norm_num [cell12962])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12962

/-! Source-cell containment and simple scalar guards at 12962. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12962)
open BstLean.Part268 (cell12962)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12962 ⟨10,by decide⟩).lower ∧ (cell12962 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12962 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12962 ⟨11,by decide⟩).lower ∧ (cell12962 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12962 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12962 ⟨12,by decide⟩).lower ∧ (cell12962 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12962 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12962 ⟨13,by decide⟩).lower ∧ (cell12962 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12962 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12962 ⟨14,by decide⟩).lower ∧ (cell12962 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12962 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12962 ⟨15,by decide⟩).lower ∧ (cell12962 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12962 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12962 ⟨16,by decide⟩).lower ∧ (cell12962 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12962 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12962 ⟨17,by decide⟩).lower ∧ (cell12962 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12962 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12962 ⟨18,by decide⟩).lower ∧ (cell12962 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12962 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12962 ⟨19,by decide⟩).lower ∧ (cell12962 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12962 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12962 ⟨20,by decide⟩).lower ∧ (cell12962 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12962 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12962 ⟨21,by decide⟩).lower ∧ (cell12962 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12962 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12962 ⟨22,by decide⟩).lower ∧ (cell12962 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12962 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12962 ⟨23,by decide⟩).lower ∧ (cell12962 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12962 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12962 ⟨24,by decide⟩).lower ∧ (cell12962 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12962 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12962 ⟨25,by decide⟩).lower ∧ (cell12962 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12962 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12962 ⟨26,by decide⟩).lower ∧ (cell12962 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12962 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12962 ⟨27,by decide⟩).lower ∧ (cell12962 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12962 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12962 ⟨28,by decide⟩).lower ∧ (cell12962 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12962 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12962 ⟨29,by decide⟩).lower ∧ (cell12962 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12962 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12962 ⟨30,by decide⟩).lower ∧ (cell12962 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12962 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12962 ⟨31,by decide⟩).lower ∧ (cell12962 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12962 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12962 ⟨32,by decide⟩).lower ∧ (cell12962 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12962 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12962 ⟨33,by decide⟩).lower ∧ (cell12962 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12962 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12962 ⟨34,by decide⟩).lower ∧ (cell12962 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12962 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12962 ⟨35,by decide⟩).lower ∧ (cell12962 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12962 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12962 ⟨36,by decide⟩).lower ∧ (cell12962 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12962 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12962 ⟨37,by decide⟩).lower ∧ (cell12962 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12962 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12962 ⟨38,by decide⟩).lower ∧ (cell12962 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12962 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12962 ⟨39,by decide⟩).lower ∧ (cell12962 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12962 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12962 ⟨40,by decide⟩).lower ∧ (cell12962 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12962 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12962 ⟨41,by decide⟩).lower ∧ (cell12962 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12962 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12962 ⟨42,by decide⟩).lower ∧ (cell12962 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12962 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12962 ⟨43,by decide⟩).lower ∧ (cell12962 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12962 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12962 ⟨44,by decide⟩).lower ∧ (cell12962 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12962 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12962 ⟨45,by decide⟩).lower ∧ (cell12962 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12962 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12962 ⟨46,by decide⟩).lower ∧ (cell12962 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12962 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12962 ⟨47,by decide⟩).lower ∧ (cell12962 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12962 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12962 ⟨48,by decide⟩).lower ∧ (cell12962 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12962 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12962 ⟨49,by decide⟩).lower ∧ (cell12962 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12962 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12962 ⟨50,by decide⟩).lower ∧ (cell12962 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12962 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12962 ⟨51,by decide⟩).lower ∧ (cell12962 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12962 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12962 ⟨52,by decide⟩).lower ∧ (cell12962 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12962 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12962 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12962 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12962,cell12962,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12962 i).lower ∧
    (cell12962 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12962 i).upper ≤ (0.532 : ℝ) ∧
    (cell12962 i).centre ≤ (0.1 : ℝ) ∧ (cell12962 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12962 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12962 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12962

/-! The local source numeric instances at 12962 have no network premises. -/
namespace BstLean.Part269.N12962
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12962)
open BstLean.Part268 (cell12962)

noncomputable def sourceNumerics12962 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12962 (cell12962 i)
      scalarRow12962.M scalarRow12962.H scalarRow12962.xi := by
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
    energy_allowance := scalarRow12962.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12962]
    centre_nonneg := (scalarRow12962.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12962])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12962