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
import BstLean.Part269Direction17
import BstLean.Part269Shared17
import BstLean.Part269Finite
import BstLean.Part269Rows17
import BstLean.Part269Source
/-! Actual 12775 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12775 ≤ (1.035703027963 : ℝ) := by
  have hr : (113.026545554573 : ℝ) ≤ √(12775 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.026545554573 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12775 12775 (11 / 1000) ≤
    (0.008457190325 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12775) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.026545554573 : ℝ) ≤ √(12775 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12775)
  have hdiv : K / √(12775 : ℝ) ≤ K / 113.026545554573 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.026545554573 ≤ (0.008457190325 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12775.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12775 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12775 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12775 := gPlus_lower 12775
end BstLean.Part269.N12775

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12775
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035703027962 : ℝ) ≤ wn 12775 := by
  have hn : √(12775 : ℝ) ≤ 113.026545554574 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12775 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.026545554574 ≤ 2 / √(12775 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250376445 : ℝ) ≤ rhoBar 12775 BstLean.Part154.csC ∧
    rhoBar 12775 BstLean.Part154.csC ≤ 0.000250376832 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035703027962 : ℝ) / (1.295212 * 12775) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035703027963 : ℝ) / (1.29521 * 12775) := by gcongr
      _ ≤ (0.000250376832 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12775 BstLean.Part154.csC) ≤ 0.001001570017 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12775 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) ≤ 0.000191239460 ∧
    cc1 (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) ≤ 0.000121686949 ∧
    cc2 (rhoBar 12775 BstLean.Part154.csC) ≤ 0.000070640220 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12775 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12775 BstLean.Part154.csC * nuR (rhoBar 12775 BstLean.Part154.csC)) ≤ 0.000500769337 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250376832 : ℝ) * 0.001001570017 := by gcongr
      _ ≤ (0.000500769337 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12775 BstLean.Part154.csC) * nuR (rhoBar 12775 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001570017 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12775 BstLean.Part154.csC) * rhoBar 12775 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250376832 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250376832 / 2 + 0.399 * 0.001001570017 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191239460 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500769337 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121686949 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250376832 / 1.414213562 := by gcongr
      _ ≤ (0.000070640220 : ℝ) := by norm_num

end BstLean.Part269.N12775

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12775
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) ≤ 1.57939E-7 := by
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12775 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12775 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191239460 : ℝ) ^ 2 + 0.000121686949 ^ 2 + 3 * 0.000070640220 ^ 2 +
        2 * 0.797885 * 0.000191239460 * 0.000121686949 + 2 * 0.000191239460 * 0.000070640220 +
        4 * 0.797885 * 0.000121686949 * 0.000070640220 := by gcongr
    _ ≤ (1.57939E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12775 BstLean.Part154.csC Θ ≤ 0.002613311337 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12775 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12775 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035703027963 * 1.57939E-7 / (0.000250376445 : ℝ) := by gcongr
    _ ≤ 0.002613311337 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12775 BstLean.Part154.csC Θ ≤ 0.002899317773 + 0.000660343019 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12775 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035703027963 : ℝ) * ((2 * Θ * 0.000250376832 +
        (6863 / 10000) * 0.000250376832 * 12775 * 0.001001570017) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002899317773 + 0.000660343019 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12775 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12775 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12775 0.011 Θ ∧ gammaRatio 12775 0.011 Θ ≤ 0.000086073081 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12775 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035703027963 : ℝ) * 0.525 / ((1 - 0.011) * 12775) := by gcongr
      _ ≤ (0.000086073081 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12775 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12775 0.011 Θ) :=
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
    badAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12775 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12775 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12775 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12775 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12775 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12775 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12775 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12775 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12775 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12775 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035703027963 : ℝ) * 12775 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003459522332 + 0.003273654356 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12775

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12775
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12775 BstLean.Part154.csC) (piBar (rhoBar 12775 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12775 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12775 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12775 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12775 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12775 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12775 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12775 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12775 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12775 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052328354345 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12775) ≤ 0.010565992044 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12775 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035703027963)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010565992044 + 2 * 0.737676 / 12775) := by gcongr
    _ ≤ (0.052328354345 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12775 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12775

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12775
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506940101 : ℝ) ≤ plow 12775 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12775) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684790869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371988452) : eMP 12775 0.011 xi bn ≤ 0.001181258192 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12775 : ℝ) * (1 - 0.011))) ≤ 0.000584078995 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371988452 / (12775 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584078995 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584078995 : ℝ) + 3.141593 * 0.052684790869 / (12775 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181258192 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684790869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371988452) : PiBarMP 12775 12 0.011 xi bn ≤ 0.160772224644 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12775 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037040362472 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.403180559982 : ℝ) ≤ √((12775 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.026545554573 : ℝ) ≤ √(12775 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12775) ≤ 0.123266690975 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037040362472 + 0.052684790869 * 1.772454 / (2 * (112.403180559982 : ℝ))) * (1 + 0.001181258192) +
        8 / (12775 * 113.026545554573) + 0.123266690975 := by gcongr
    _ ≤ (0.160772224644 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684790869)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371988452) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281860031612) :
    parallelOracle 12775 0.011 xi bn cd ≤ 0.161756881959 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12775 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12775 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506940101 : ℝ) ≤ plow 12775 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.026545554573 : ℝ) ≤ √(12775 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281860031612 : ℝ) / (2 * 0.560506940101 * 113.026545554573)) * 0.160772224644 +
        0.281860031612 ^ 2 / (2 * 0.560506940101 * 113.026545554573) := by gcongr
    _ ≤ (0.161756881959 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684790869) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371988452)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281860031612) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12775 12775 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506940101 : ℝ) ≤ plow 12775 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.026545554573 : ℝ) ≤ √(12775 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12775 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12775 Θ 1.22 ≤ 0.011732646464 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.026545554573 := by gcongr <;> linarith
      _ ≤ (0.011732646464 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12775 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12775 12775 0.011 ≤ 0.008457190325 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12775 12775 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12775 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12775 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12775 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12775 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161756881959 + 0.011732646464 + (0.008457190325 : ℝ) *
        (1 + 2 * (0.281860031612 + 0.011732646464) / (0.560506940101 * 113.026545554573))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12775]

end BstLean.Part269.N12775

/-! The original eight local profiles supply actual 12775 moment certificates. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12775 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052684790869 ∧
    0 ≤ bN 12775 BstLean.Part154.csC (groupTheta g) ∧ bN 12775 BstLean.Part154.csC (groupTheta g) ≤ 0.001371988452 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12775 12775 0.011
      (momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12775 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12775 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12775 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229531677267 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12775 0.011
      (momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12775 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12775
/-! The actual computed-centre upper energy formula at 12775. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12775

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12775)
open BstLean.Part268 (cell12775)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085274507342
  | 2 => 0.086213359385
  | 3 => 0.087149793332
  | 4 => 0.088085098009
  | 5 => 0.089020836462
  | 6 => 0.089958887220
  | 7 => 0.090901489533
  | 8 => 0.091851292657
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12775 12775 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12775 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12775

/-! Actual upper energy certificates on all 43 source endpoints at 12775. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12775)
open BstLean.Part268 (cell12775)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12775 (gMinus 12775) (1 - (cell12775 i).lower) ≤ 1 ∧
    energyUpper 12775 (gMinus 12775) (BstLean.Part211.gPlus 12775)
      (finiteEnergy 12775 12775 0.011) (1 - (cell12775 i).lower) ≤
      (cell12775 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨10,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨11,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨12,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨13,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨14,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨15,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨16,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨17,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨18,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨19,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨20,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨21,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨22,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨23,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨24,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨25,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨26,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨27,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨28,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨29,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨30,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨31,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨32,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨33,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨34,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨35,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨36,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨37,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨38,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨39,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨40,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨41,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨42,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨43,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨44,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨45,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨46,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨47,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨48,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨49,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨50,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨51,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12775) (by norm_num)
        (q := 1 - (cell12775 ⟨52,by decide⟩).lower)
        (by norm_num [cell12775]) (by norm_num [cell12775])
      exact ⟨E.1,E.2.trans (by norm_num [cell12775])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12775

/-! Source-cell containment and simple scalar guards at 12775. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12775)
open BstLean.Part268 (cell12775)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12775 ⟨10,by decide⟩).lower ∧ (cell12775 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12775 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12775 ⟨11,by decide⟩).lower ∧ (cell12775 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12775 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12775 ⟨12,by decide⟩).lower ∧ (cell12775 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12775 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12775 ⟨13,by decide⟩).lower ∧ (cell12775 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12775 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12775 ⟨14,by decide⟩).lower ∧ (cell12775 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12775 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12775 ⟨15,by decide⟩).lower ∧ (cell12775 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12775 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12775 ⟨16,by decide⟩).lower ∧ (cell12775 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12775 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12775 ⟨17,by decide⟩).lower ∧ (cell12775 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12775 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12775 ⟨18,by decide⟩).lower ∧ (cell12775 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12775 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12775 ⟨19,by decide⟩).lower ∧ (cell12775 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12775 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12775 ⟨20,by decide⟩).lower ∧ (cell12775 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12775 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12775 ⟨21,by decide⟩).lower ∧ (cell12775 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12775 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12775 ⟨22,by decide⟩).lower ∧ (cell12775 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12775 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12775 ⟨23,by decide⟩).lower ∧ (cell12775 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12775 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12775 ⟨24,by decide⟩).lower ∧ (cell12775 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12775 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12775 ⟨25,by decide⟩).lower ∧ (cell12775 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12775 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12775 ⟨26,by decide⟩).lower ∧ (cell12775 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12775 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12775 ⟨27,by decide⟩).lower ∧ (cell12775 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12775 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12775 ⟨28,by decide⟩).lower ∧ (cell12775 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12775 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12775 ⟨29,by decide⟩).lower ∧ (cell12775 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12775 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12775 ⟨30,by decide⟩).lower ∧ (cell12775 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12775 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12775 ⟨31,by decide⟩).lower ∧ (cell12775 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12775 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12775 ⟨32,by decide⟩).lower ∧ (cell12775 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12775 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12775 ⟨33,by decide⟩).lower ∧ (cell12775 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12775 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12775 ⟨34,by decide⟩).lower ∧ (cell12775 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12775 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12775 ⟨35,by decide⟩).lower ∧ (cell12775 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12775 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12775 ⟨36,by decide⟩).lower ∧ (cell12775 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12775 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12775 ⟨37,by decide⟩).lower ∧ (cell12775 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12775 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12775 ⟨38,by decide⟩).lower ∧ (cell12775 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12775 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12775 ⟨39,by decide⟩).lower ∧ (cell12775 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12775 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12775 ⟨40,by decide⟩).lower ∧ (cell12775 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12775 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12775 ⟨41,by decide⟩).lower ∧ (cell12775 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12775 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12775 ⟨42,by decide⟩).lower ∧ (cell12775 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12775 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12775 ⟨43,by decide⟩).lower ∧ (cell12775 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12775 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12775 ⟨44,by decide⟩).lower ∧ (cell12775 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12775 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12775 ⟨45,by decide⟩).lower ∧ (cell12775 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12775 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12775 ⟨46,by decide⟩).lower ∧ (cell12775 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12775 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12775 ⟨47,by decide⟩).lower ∧ (cell12775 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12775 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12775 ⟨48,by decide⟩).lower ∧ (cell12775 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12775 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12775 ⟨49,by decide⟩).lower ∧ (cell12775 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12775 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12775 ⟨50,by decide⟩).lower ∧ (cell12775 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12775 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12775 ⟨51,by decide⟩).lower ∧ (cell12775 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12775 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12775 ⟨52,by decide⟩).lower ∧ (cell12775 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12775 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12775 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12775 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12775,cell12775,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12775 i).lower ∧
    (cell12775 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12775 i).upper ≤ (0.532 : ℝ) ∧
    (cell12775 i).centre ≤ (0.1 : ℝ) ∧ (cell12775 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12775 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12775 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12775

/-! The local source numeric instances at 12775 have no network premises. -/
namespace BstLean.Part269.N12775
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12775)
open BstLean.Part268 (cell12775)

noncomputable def sourceNumerics12775 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12775 (cell12775 i)
      scalarRow12775.M scalarRow12775.H scalarRow12775.xi := by
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
    energy_allowance := scalarRow12775.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12775]
    centre_nonneg := (scalarRow12775.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12775])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12775
/-! Actual 12776 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12776 ≤ (1.035701618412 : ℝ) := by
  have hr : (113.030969207558 : ℝ) ≤ √(12776 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.030969207558 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12776 12776 (11 / 1000) ≤
    (0.008456859337 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12776) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.030969207558 : ℝ) ≤ √(12776 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12776)
  have hdiv : K / √(12776 : ℝ) ≤ K / 113.030969207558 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.030969207558 ≤ (0.008456859337 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12776.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12776 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12776 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12776 := gPlus_lower 12776
end BstLean.Part269.N12776

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12776
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035701618411 : ℝ) ≤ wn 12776 := by
  have hn : √(12776 : ℝ) ≤ 113.030969207559 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12776 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.030969207559 ≤ 2 / √(12776 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250356507 : ℝ) ≤ rhoBar 12776 BstLean.Part154.csC ∧
    rhoBar 12776 BstLean.Part154.csC ≤ 0.000250356894 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035701618411 : ℝ) / (1.295212 * 12776) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035701618412 : ℝ) / (1.29521 * 12776) := by gcongr
      _ ≤ (0.000250356894 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12776 BstLean.Part154.csC) ≤ 0.001001490255 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12776 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) ≤ 0.000191224231 ∧
    cc1 (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) ≤ 0.000121677259 ∧
    cc2 (rhoBar 12776 BstLean.Part154.csC) ≤ 0.000070634594 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12776 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12776 BstLean.Part154.csC * nuR (rhoBar 12776 BstLean.Part154.csC)) ≤ 0.000500729458 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250356894 : ℝ) * 0.001001490255 := by gcongr
      _ ≤ (0.000500729458 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12776 BstLean.Part154.csC) * nuR (rhoBar 12776 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001490255 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12776 BstLean.Part154.csC) * rhoBar 12776 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250356894 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250356894 / 2 + 0.399 * 0.001001490255 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191224231 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500729458 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121677259 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250356894 / 1.414213562 := by gcongr
      _ ≤ (0.000070634594 : ℝ) := by norm_num

end BstLean.Part269.N12776

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12776
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) ≤ 1.57914E-7 := by
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12776 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12776 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191224231 : ℝ) ^ 2 + 0.000121677259 ^ 2 + 3 * 0.000070634594 ^ 2 +
        2 * 0.797885 * 0.000191224231 * 0.000121677259 + 2 * 0.000191224231 * 0.000070634594 +
        4 * 0.797885 * 0.000121677259 * 0.000070634594 := by gcongr
    _ ≤ (1.57914E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12776 BstLean.Part154.csC Θ ≤ 0.002613102210 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12776 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12776 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035701618412 * 1.57914E-7 / (0.000250356507 : ℝ) := by gcongr
    _ ≤ 0.002613102210 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12776 BstLean.Part154.csC Θ ≤ 0.002899078991 + 0.000660289536 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12776 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035701618412 : ℝ) * ((2 * Θ * 0.000250356894 +
        (6863 / 10000) * 0.000250356894 * 12776 * 0.001001490255) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002899078991 + 0.000660289536 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12776 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12776 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12776 0.011 Θ ∧ gammaRatio 12776 0.011 Θ ≤ 0.000086066226 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12776 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035701618412 : ℝ) * 0.525 / ((1 - 0.011) * 12776) := by gcongr
      _ ≤ (0.000086066226 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12776 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12776 0.011 Θ) :=
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
    badAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12776 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12776 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12776 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12776 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12776 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12776 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12776 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12776 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12776 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12776 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035701618412 : ℝ) * 12776 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003459283550 + 0.003273391746 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12776

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12776
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12776 BstLean.Part154.csC) (piBar (rhoBar 12776 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12776 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12776 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12776 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12776 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12776 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12776 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12776 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12776 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12776 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052326284250 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12776) ≤ 0.010565578527 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12776 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035701618412)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010565578527 + 2 * 0.737676 / 12776) := by gcongr
    _ ≤ (0.052326284250 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12776 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12776

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12776
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506984791 : ℝ) ≤ plow 12776 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12776) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684414217)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371878661) : eMP 12776 0.011 xi bn ≤ 0.001181164617 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12776 : ℝ) * (1 - 0.011))) ≤ 0.000584032767 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371878661 / (12776 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584032767 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584032767 : ℝ) + 3.141593 * 0.052684414217 / (12776 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181164617 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684414217)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371878661) : PiBarMP 12776 12 0.011 xi bn ≤ 0.160765893169 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12776 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037038880397 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.407579815597 : ℝ) ≤ √((12776 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.030969207558 : ℝ) ≤ √(12776 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12776) ≤ 0.123261866730 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037038880397 + 0.052684414217 * 1.772454 / (2 * (112.407579815597 : ℝ))) * (1 + 0.001181164617) +
        8 / (12776 * 113.030969207558) + 0.123261866730 := by gcongr
    _ ≤ (0.160765893169 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684414217)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371878661) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281857141037) :
    parallelOracle 12776 0.011 xi bn cd ≤ 0.161750481258 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12776 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12776 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506984791 : ℝ) ≤ plow 12776 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.030969207558 : ℝ) ≤ √(12776 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281857141037 : ℝ) / (2 * 0.560506984791 * 113.030969207558)) * 0.160765893169 +
        0.281857141037 ^ 2 / (2 * 0.560506984791 * 113.030969207558) := by gcongr
    _ ≤ (0.161750481258 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684414217) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371878661)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281857141037) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12776 12776 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506984791 : ℝ) ≤ plow 12776 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.030969207558 : ℝ) ≤ √(12776 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12776 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12776 Θ 1.22 ≤ 0.011732187288 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.030969207558 := by gcongr <;> linarith
      _ ≤ (0.011732187288 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12776 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12776 12776 0.011 ≤ 0.008456859337 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12776 12776 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12776 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12776 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12776 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12776 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161750481258 + 0.011732187288 + (0.008456859337 : ℝ) *
        (1 + 2 * (0.281857141037 + 0.011732187288) / (0.560506984791 * 113.030969207558))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12776]

end BstLean.Part269.N12776

/-! The original eight local profiles supply actual 12776 moment certificates. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12776 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052684414217 ∧
    0 ≤ bN 12776 BstLean.Part154.csC (groupTheta g) ∧ bN 12776 BstLean.Part154.csC (groupTheta g) ≤ 0.001371878661 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12776 12776 0.011
      (momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12776 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12776 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12776 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229530856787 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12776 0.011
      (momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12776 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12776
/-! The actual computed-centre upper energy formula at 12776. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12776

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12776)
open BstLean.Part268 (cell12776)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085271669855
  | 2 => 0.086210471520
  | 3 => 0.087146848024
  | 4 => 0.088082086548
  | 5 => 0.089017748197
  | 6 => 0.089955709227
  | 7 => 0.090898206245
  | 8 => 0.091847885452
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12776 12776 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12776 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12776

/-! Actual upper energy certificates on all 43 source endpoints at 12776. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12776)
open BstLean.Part268 (cell12776)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12776 (gMinus 12776) (1 - (cell12776 i).lower) ≤ 1 ∧
    energyUpper 12776 (gMinus 12776) (BstLean.Part211.gPlus 12776)
      (finiteEnergy 12776 12776 0.011) (1 - (cell12776 i).lower) ≤
      (cell12776 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨10,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨11,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨12,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨13,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨14,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨15,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨16,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨17,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨18,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨19,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨20,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨21,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨22,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨23,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨24,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨25,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨26,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨27,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨28,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨29,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨30,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨31,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨32,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨33,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨34,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨35,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨36,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨37,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨38,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨39,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨40,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨41,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨42,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨43,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨44,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨45,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨46,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨47,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨48,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨49,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨50,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨51,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12776) (by norm_num)
        (q := 1 - (cell12776 ⟨52,by decide⟩).lower)
        (by norm_num [cell12776]) (by norm_num [cell12776])
      exact ⟨E.1,E.2.trans (by norm_num [cell12776])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12776

/-! Source-cell containment and simple scalar guards at 12776. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12776)
open BstLean.Part268 (cell12776)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12776 ⟨10,by decide⟩).lower ∧ (cell12776 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12776 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12776 ⟨11,by decide⟩).lower ∧ (cell12776 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12776 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12776 ⟨12,by decide⟩).lower ∧ (cell12776 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12776 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12776 ⟨13,by decide⟩).lower ∧ (cell12776 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12776 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12776 ⟨14,by decide⟩).lower ∧ (cell12776 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12776 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12776 ⟨15,by decide⟩).lower ∧ (cell12776 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12776 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12776 ⟨16,by decide⟩).lower ∧ (cell12776 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12776 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12776 ⟨17,by decide⟩).lower ∧ (cell12776 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12776 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12776 ⟨18,by decide⟩).lower ∧ (cell12776 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12776 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12776 ⟨19,by decide⟩).lower ∧ (cell12776 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12776 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12776 ⟨20,by decide⟩).lower ∧ (cell12776 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12776 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12776 ⟨21,by decide⟩).lower ∧ (cell12776 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12776 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12776 ⟨22,by decide⟩).lower ∧ (cell12776 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12776 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12776 ⟨23,by decide⟩).lower ∧ (cell12776 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12776 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12776 ⟨24,by decide⟩).lower ∧ (cell12776 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12776 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12776 ⟨25,by decide⟩).lower ∧ (cell12776 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12776 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12776 ⟨26,by decide⟩).lower ∧ (cell12776 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12776 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12776 ⟨27,by decide⟩).lower ∧ (cell12776 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12776 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12776 ⟨28,by decide⟩).lower ∧ (cell12776 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12776 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12776 ⟨29,by decide⟩).lower ∧ (cell12776 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12776 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12776 ⟨30,by decide⟩).lower ∧ (cell12776 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12776 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12776 ⟨31,by decide⟩).lower ∧ (cell12776 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12776 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12776 ⟨32,by decide⟩).lower ∧ (cell12776 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12776 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12776 ⟨33,by decide⟩).lower ∧ (cell12776 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12776 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12776 ⟨34,by decide⟩).lower ∧ (cell12776 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12776 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12776 ⟨35,by decide⟩).lower ∧ (cell12776 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12776 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12776 ⟨36,by decide⟩).lower ∧ (cell12776 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12776 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12776 ⟨37,by decide⟩).lower ∧ (cell12776 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12776 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12776 ⟨38,by decide⟩).lower ∧ (cell12776 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12776 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12776 ⟨39,by decide⟩).lower ∧ (cell12776 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12776 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12776 ⟨40,by decide⟩).lower ∧ (cell12776 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12776 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12776 ⟨41,by decide⟩).lower ∧ (cell12776 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12776 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12776 ⟨42,by decide⟩).lower ∧ (cell12776 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12776 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12776 ⟨43,by decide⟩).lower ∧ (cell12776 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12776 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12776 ⟨44,by decide⟩).lower ∧ (cell12776 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12776 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12776 ⟨45,by decide⟩).lower ∧ (cell12776 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12776 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12776 ⟨46,by decide⟩).lower ∧ (cell12776 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12776 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12776 ⟨47,by decide⟩).lower ∧ (cell12776 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12776 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12776 ⟨48,by decide⟩).lower ∧ (cell12776 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12776 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12776 ⟨49,by decide⟩).lower ∧ (cell12776 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12776 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12776 ⟨50,by decide⟩).lower ∧ (cell12776 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12776 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12776 ⟨51,by decide⟩).lower ∧ (cell12776 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12776 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12776 ⟨52,by decide⟩).lower ∧ (cell12776 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12776 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12776 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12776 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12776,cell12776,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12776 i).lower ∧
    (cell12776 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12776 i).upper ≤ (0.532 : ℝ) ∧
    (cell12776 i).centre ≤ (0.1 : ℝ) ∧ (cell12776 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12776 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12776 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12776

/-! The local source numeric instances at 12776 have no network premises. -/
namespace BstLean.Part269.N12776
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12776)
open BstLean.Part268 (cell12776)

noncomputable def sourceNumerics12776 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12776 (cell12776 i)
      scalarRow12776.M scalarRow12776.H scalarRow12776.xi := by
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
    energy_allowance := scalarRow12776.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12776]
    centre_nonneg := (scalarRow12776.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12776])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12776
/-! Actual 12777 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12777 ≤ (1.035700209028 : ℝ) := by
  have hr : (113.035392687423 : ℝ) ≤ √(12777 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.035392687423 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12777 12777 (11 / 1000) ≤
    (0.008456528387 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12777) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.035392687423 : ℝ) ≤ √(12777 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12777)
  have hdiv : K / √(12777 : ℝ) ≤ K / 113.035392687423 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.035392687423 ≤ (0.008456528387 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12777.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12777 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12777 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12777 := gPlus_lower 12777
end BstLean.Part269.N12777

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12777
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035700209027 : ℝ) ≤ wn 12777 := by
  have hn : √(12777 : ℝ) ≤ 113.035392687424 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12777 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.035392687424 ≤ 2 / √(12777 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250336572 : ℝ) ≤ rhoBar 12777 BstLean.Part154.csC ∧
    rhoBar 12777 BstLean.Part154.csC ≤ 0.000250336959 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035700209027 : ℝ) / (1.295212 * 12777) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035700209028 : ℝ) / (1.29521 * 12777) := by gcongr
      _ ≤ (0.000250336959 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12777 BstLean.Part154.csC) ≤ 0.001001410505 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12777 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) ≤ 0.000191209004 ∧
    cc1 (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) ≤ 0.000121667570 ∧
    cc2 (rhoBar 12777 BstLean.Part154.csC) ≤ 0.000070628970 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12777 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12777 BstLean.Part154.csC * nuR (rhoBar 12777 BstLean.Part154.csC)) ≤ 0.000500689586 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250336959 : ℝ) * 0.001001410505 := by gcongr
      _ ≤ (0.000500689586 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12777 BstLean.Part154.csC) * nuR (rhoBar 12777 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001410505 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12777 BstLean.Part154.csC) * rhoBar 12777 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250336959 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250336959 / 2 + 0.399 * 0.001001410505 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191209004 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500689586 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121667570 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250336959 / 1.414213562 := by gcongr
      _ ≤ (0.000070628970 : ℝ) := by norm_num

end BstLean.Part269.N12777

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12777
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) ≤ 1.57889E-7 := by
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12777 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12777 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191209004 : ℝ) ^ 2 + 0.000121667570 ^ 2 + 3 * 0.000070628970 ^ 2 +
        2 * 0.797885 * 0.000191209004 * 0.000121667570 + 2 * 0.000191209004 * 0.000070628970 +
        4 * 0.797885 * 0.000121667570 * 0.000070628970 := by gcongr
    _ ≤ (1.57889E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12777 BstLean.Part154.csC Θ ≤ 0.002612893019 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12777 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12777 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035700209028 * 1.57889E-7 / (0.000250336572 : ℝ) := by gcongr
    _ ≤ 0.002612893019 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12777 BstLean.Part154.csC Θ ≤ 0.002898840244 + 0.000660236061 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12777 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035700209028 : ℝ) * ((2 * Θ * 0.000250336959 +
        (6863 / 10000) * 0.000250336959 * 12777 * 0.001001410505) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002898840244 + 0.000660236061 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12777 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12777 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12777 0.011 Θ ∧ gammaRatio 12777 0.011 Θ ≤ 0.000086059373 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12777 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035700209028 : ℝ) * 0.525 / ((1 - 0.011) * 12777) := by gcongr
      _ ≤ (0.000086059373 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12777 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12777 0.011 Θ) :=
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
    badAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12777 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12777 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12777 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12777 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12777 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12777 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12777 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12777 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12777 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12777 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035700209028 : ℝ) * 12777 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003459044803 + 0.003273129080 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12777

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12777
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12777 BstLean.Part154.csC) (piBar (rhoBar 12777 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12777 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12777 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12777 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12777 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12777 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12777 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12777 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12777 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12777 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052324214397 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12777) ≤ 0.010565165058 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12777 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035700209028)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010565165058 + 2 * 0.737676 / 12777) := by gcongr
    _ ≤ (0.052324214397 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12777 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12777

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12777
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507029474 : ℝ) ≤ plow 12777 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12777) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684037570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371768835) : eMP 12777 0.011 xi bn ≤ 0.001181071034 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12777 : ℝ) * (1 - 0.011))) ≤ 0.000583986535 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371768835 / (12777 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583986535 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583986535 : ℝ) + 3.141593 * 0.052684037570 / (12777 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181071034 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684037570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371768835) : PiBarMP 12777 12 0.011 xi bn ≤ 0.160759561730 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12777 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037037397790 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.411978899047 : ℝ) ≤ √((12777 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.035392687423 : ℝ) ≤ √(12777 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12777) ≤ 0.123257043051 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037037397790 + 0.052684037570 * 1.772454 / (2 * (112.411978899047 : ℝ))) * (1 + 0.001181071034) +
        8 / (12777 * 113.035392687423) + 0.123257043051 := by gcongr
    _ ≤ (0.160759561730 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684037570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371768835) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281854250711) :
    parallelOracle 12777 0.011 xi bn cd ≤ 0.161744080601 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12777 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12777 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507029474 : ℝ) ≤ plow 12777 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.035392687423 : ℝ) ≤ √(12777 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281854250711 : ℝ) / (2 * 0.560507029474 * 113.035392687423)) * 0.160759561730 +
        0.281854250711 ^ 2 / (2 * 0.560507029474 * 113.035392687423) := by gcongr
    _ ≤ (0.161744080601 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052684037570) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371768835)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281854250711) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12777 12777 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507029474 : ℝ) ≤ plow 12777 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.035392687423 : ℝ) ≤ √(12777 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12777 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12777 Θ 1.22 ≤ 0.011731728165 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.035392687423 := by gcongr <;> linarith
      _ ≤ (0.011731728165 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12777 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12777 12777 0.011 ≤ 0.008456528387 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12777 12777 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12777 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12777 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12777 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12777 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161744080601 + 0.011731728165 + (0.008456528387 : ℝ) *
        (1 + 2 * (0.281854250711 + 0.011731728165) / (0.560507029474 * 113.035392687423))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12777]

end BstLean.Part269.N12777

/-! The original eight local profiles supply actual 12777 moment certificates. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12777 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052684037570 ∧
    0 ≤ bN 12777 BstLean.Part154.csC (groupTheta g) ∧ bN 12777 BstLean.Part154.csC (groupTheta g) ≤ 0.001371768835 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12777 12777 0.011
      (momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12777 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12777 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12777 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229530036314 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12777 0.011
      (momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12777 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12777
/-! The actual computed-centre upper energy formula at 12777. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12777

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12777)
open BstLean.Part268 (cell12777)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085268833372
  | 2 => 0.086207584699
  | 3 => 0.087143903810
  | 4 => 0.088079076243
  | 5 => 0.089014661162
  | 6 => 0.089952532555
  | 7 => 0.090894924389
  | 8 => 0.091844479812
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12777 12777 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12777 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12777

/-! Actual upper energy certificates on all 43 source endpoints at 12777. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12777)
open BstLean.Part268 (cell12777)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12777 (gMinus 12777) (1 - (cell12777 i).lower) ≤ 1 ∧
    energyUpper 12777 (gMinus 12777) (BstLean.Part211.gPlus 12777)
      (finiteEnergy 12777 12777 0.011) (1 - (cell12777 i).lower) ≤
      (cell12777 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨10,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨11,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨12,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨13,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨14,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨15,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨16,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨17,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨18,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨19,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨20,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨21,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨22,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨23,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨24,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨25,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨26,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨27,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨28,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨29,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨30,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨31,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨32,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨33,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨34,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨35,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨36,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨37,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨38,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨39,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨40,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨41,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨42,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨43,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨44,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨45,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨46,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨47,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨48,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨49,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨50,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨51,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12777) (by norm_num)
        (q := 1 - (cell12777 ⟨52,by decide⟩).lower)
        (by norm_num [cell12777]) (by norm_num [cell12777])
      exact ⟨E.1,E.2.trans (by norm_num [cell12777])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12777

/-! Source-cell containment and simple scalar guards at 12777. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12777)
open BstLean.Part268 (cell12777)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12777 ⟨10,by decide⟩).lower ∧ (cell12777 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12777 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12777 ⟨11,by decide⟩).lower ∧ (cell12777 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12777 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12777 ⟨12,by decide⟩).lower ∧ (cell12777 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12777 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12777 ⟨13,by decide⟩).lower ∧ (cell12777 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12777 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12777 ⟨14,by decide⟩).lower ∧ (cell12777 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12777 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12777 ⟨15,by decide⟩).lower ∧ (cell12777 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12777 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12777 ⟨16,by decide⟩).lower ∧ (cell12777 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12777 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12777 ⟨17,by decide⟩).lower ∧ (cell12777 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12777 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12777 ⟨18,by decide⟩).lower ∧ (cell12777 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12777 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12777 ⟨19,by decide⟩).lower ∧ (cell12777 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12777 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12777 ⟨20,by decide⟩).lower ∧ (cell12777 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12777 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12777 ⟨21,by decide⟩).lower ∧ (cell12777 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12777 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12777 ⟨22,by decide⟩).lower ∧ (cell12777 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12777 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12777 ⟨23,by decide⟩).lower ∧ (cell12777 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12777 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12777 ⟨24,by decide⟩).lower ∧ (cell12777 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12777 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12777 ⟨25,by decide⟩).lower ∧ (cell12777 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12777 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12777 ⟨26,by decide⟩).lower ∧ (cell12777 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12777 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12777 ⟨27,by decide⟩).lower ∧ (cell12777 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12777 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12777 ⟨28,by decide⟩).lower ∧ (cell12777 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12777 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12777 ⟨29,by decide⟩).lower ∧ (cell12777 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12777 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12777 ⟨30,by decide⟩).lower ∧ (cell12777 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12777 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12777 ⟨31,by decide⟩).lower ∧ (cell12777 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12777 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12777 ⟨32,by decide⟩).lower ∧ (cell12777 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12777 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12777 ⟨33,by decide⟩).lower ∧ (cell12777 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12777 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12777 ⟨34,by decide⟩).lower ∧ (cell12777 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12777 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12777 ⟨35,by decide⟩).lower ∧ (cell12777 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12777 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12777 ⟨36,by decide⟩).lower ∧ (cell12777 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12777 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12777 ⟨37,by decide⟩).lower ∧ (cell12777 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12777 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12777 ⟨38,by decide⟩).lower ∧ (cell12777 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12777 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12777 ⟨39,by decide⟩).lower ∧ (cell12777 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12777 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12777 ⟨40,by decide⟩).lower ∧ (cell12777 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12777 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12777 ⟨41,by decide⟩).lower ∧ (cell12777 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12777 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12777 ⟨42,by decide⟩).lower ∧ (cell12777 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12777 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12777 ⟨43,by decide⟩).lower ∧ (cell12777 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12777 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12777 ⟨44,by decide⟩).lower ∧ (cell12777 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12777 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12777 ⟨45,by decide⟩).lower ∧ (cell12777 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12777 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12777 ⟨46,by decide⟩).lower ∧ (cell12777 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12777 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12777 ⟨47,by decide⟩).lower ∧ (cell12777 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12777 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12777 ⟨48,by decide⟩).lower ∧ (cell12777 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12777 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12777 ⟨49,by decide⟩).lower ∧ (cell12777 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12777 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12777 ⟨50,by decide⟩).lower ∧ (cell12777 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12777 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12777 ⟨51,by decide⟩).lower ∧ (cell12777 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12777 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12777 ⟨52,by decide⟩).lower ∧ (cell12777 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12777 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12777 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12777 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12777,cell12777,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12777 i).lower ∧
    (cell12777 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12777 i).upper ≤ (0.532 : ℝ) ∧
    (cell12777 i).centre ≤ (0.1 : ℝ) ∧ (cell12777 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12777 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12777 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12777

/-! The local source numeric instances at 12777 have no network premises. -/
namespace BstLean.Part269.N12777
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12777)
open BstLean.Part268 (cell12777)

noncomputable def sourceNumerics12777 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12777 (cell12777 i)
      scalarRow12777.M scalarRow12777.H scalarRow12777.xi := by
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
    energy_allowance := scalarRow12777.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12777]
    centre_nonneg := (scalarRow12777.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12777])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12777
/-! Actual 12778 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12778 ≤ (1.035698799811 : ℝ) := by
  have hr : (113.039815994188 : ℝ) ≤ √(12778 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.039815994188 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12778 12778 (11 / 1000) ≤
    (0.008456197476 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12778) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.039815994188 : ℝ) ≤ √(12778 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12778)
  have hdiv : K / √(12778 : ℝ) ≤ K / 113.039815994188 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.039815994188 ≤ (0.008456197476 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12778.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12778 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12778 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12778 := gPlus_lower 12778
end BstLean.Part269.N12778

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12778
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035698799810 : ℝ) ≤ wn 12778 := by
  have hn : √(12778 : ℝ) ≤ 113.039815994189 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12778 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.039815994189 ≤ 2 / √(12778 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250316640 : ℝ) ≤ rhoBar 12778 BstLean.Part154.csC ∧
    rhoBar 12778 BstLean.Part154.csC ≤ 0.000250317027 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035698799810 : ℝ) / (1.295212 * 12778) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035698799811 : ℝ) / (1.29521 * 12778) := by gcongr
      _ ≤ (0.000250317027 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12778 BstLean.Part154.csC) ≤ 0.001001330767 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12778 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) ≤ 0.000191193779 ∧
    cc1 (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) ≤ 0.000121657882 ∧
    cc2 (rhoBar 12778 BstLean.Part154.csC) ≤ 0.000070623347 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12778 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12778 BstLean.Part154.csC * nuR (rhoBar 12778 BstLean.Part154.csC)) ≤ 0.000500649719 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250317027 : ℝ) * 0.001001330767 := by gcongr
      _ ≤ (0.000500649719 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12778 BstLean.Part154.csC) * nuR (rhoBar 12778 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001330767 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12778 BstLean.Part154.csC) * rhoBar 12778 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250317027 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250317027 / 2 + 0.399 * 0.001001330767 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191193779 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500649719 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121657882 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250317027 / 1.414213562 := by gcongr
      _ ≤ (0.000070623347 : ℝ) := by norm_num

end BstLean.Part269.N12778

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12778
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) ≤ 1.57864E-7 := by
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12778 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12778 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191193779 : ℝ) ^ 2 + 0.000121657882 ^ 2 + 3 * 0.000070623347 ^ 2 +
        2 * 0.797885 * 0.000191193779 * 0.000121657882 + 2 * 0.000191193779 * 0.000070623347 +
        4 * 0.797885 * 0.000121657882 * 0.000070623347 := by gcongr
    _ ≤ (1.57864E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12778 BstLean.Part154.csC Θ ≤ 0.002612683765 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12778 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12778 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035698799811 * 1.57864E-7 / (0.000250316640 : ℝ) := by gcongr
    _ ≤ 0.002612683765 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12778 BstLean.Part154.csC Θ ≤ 0.002898601532 + 0.000660182594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12778 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035698799811 : ℝ) * ((2 * Θ * 0.000250317027 +
        (6863 / 10000) * 0.000250317027 * 12778 * 0.001001330767) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002898601532 + 0.000660182594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12778 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12778 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12778 0.011 Θ ∧ gammaRatio 12778 0.011 Θ ≤ 0.000086052521 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12778 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035698799811 : ℝ) * 0.525 / ((1 - 0.011) * 12778) := by gcongr
      _ ≤ (0.000086052521 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12778 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12778 0.011 Θ) :=
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
    badAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12778 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12778 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12778 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12778 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12778 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12778 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12778 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12778 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12778 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12778 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035698799811 : ℝ) * 12778 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003458806091 + 0.003272866359 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12778

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12778
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12778 BstLean.Part154.csC) (piBar (rhoBar 12778 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12778 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12778 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12778 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12778 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12778 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12778 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12778 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12778 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12778 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052322144786 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12778) ≤ 0.010564751637 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12778 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035698799811)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010564751637 + 2 * 0.737676 / 12778) := by gcongr
    _ ≤ (0.052322144786 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12778 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12778

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12778
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507074150 : ℝ) ≤ plow 12778 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12778) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683660930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371658977) : eMP 12778 0.011 xi bn ≤ 0.001180977444 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12778 : ℝ) * (1 - 0.011))) ≤ 0.000583940299 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371658977 / (12778 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583940299 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583940299 : ℝ) + 3.141593 * 0.052683660930 / (12778 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180977444 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683660930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371658977) : PiBarMP 12778 12 0.011 xi bn ≤ 0.160753230368 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12778 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037035914692 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.416377810352 : ℝ) ≤ √((12778 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.039815994188 : ℝ) ≤ √(12778 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12778) ≤ 0.123252219939 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037035914692 + 0.052683660930 * 1.772454 / (2 * (112.416377810352 : ℝ))) * (1 + 0.001180977444) +
        8 / (12778 * 113.039815994188) + 0.123252219939 := by gcongr
    _ ≤ (0.160753230368 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683660930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371658977) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281851360639) :
    parallelOracle 12778 0.011 xi bn cd ≤ 0.161737680031 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12778 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12778 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507074150 : ℝ) ≤ plow 12778 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.039815994188 : ℝ) ≤ √(12778 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281851360639 : ℝ) / (2 * 0.560507074150 * 113.039815994188)) * 0.160753230368 +
        0.281851360639 ^ 2 / (2 * 0.560507074150 * 113.039815994188) := by gcongr
    _ ≤ (0.161737680031 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683660930) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371658977)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281851360639) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12778 12778 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507074150 : ℝ) ≤ plow 12778 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.039815994188 : ℝ) ≤ √(12778 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12778 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12778 Θ 1.22 ≤ 0.011731269097 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.039815994188 := by gcongr <;> linarith
      _ ≤ (0.011731269097 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12778 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12778 12778 0.011 ≤ 0.008456197476 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12778 12778 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12778 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12778 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12778 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12778 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161737680031 + 0.011731269097 + (0.008456197476 : ℝ) *
        (1 + 2 * (0.281851360639 + 0.011731269097) / (0.560507074150 * 113.039815994188))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12778]

end BstLean.Part269.N12778

/-! The original eight local profiles supply actual 12778 moment certificates. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12778 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052683660930 ∧
    0 ≤ bN 12778 BstLean.Part154.csC (groupTheta g) ∧ bN 12778 BstLean.Part154.csC (groupTheta g) ≤ 0.001371658977 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12778 12778 0.011
      (momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12778 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12778 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12778 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229529215853 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12778 0.011
      (momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12778 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12778
/-! The actual computed-centre upper energy formula at 12778. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12778

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12778)
open BstLean.Part268 (cell12778)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085265997893
  | 2 => 0.086204698922
  | 3 => 0.087140960690
  | 4 => 0.088076067092
  | 5 => 0.089011575357
  | 6 => 0.089949357204
  | 7 => 0.090891643964
  | 8 => 0.091841075736
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12778 12778 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12778 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12778

/-! Actual upper energy certificates on all 43 source endpoints at 12778. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12778)
open BstLean.Part268 (cell12778)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12778 (gMinus 12778) (1 - (cell12778 i).lower) ≤ 1 ∧
    energyUpper 12778 (gMinus 12778) (BstLean.Part211.gPlus 12778)
      (finiteEnergy 12778 12778 0.011) (1 - (cell12778 i).lower) ≤
      (cell12778 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨10,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨11,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨12,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨13,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨14,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨15,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨16,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨17,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨18,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨19,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨20,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨21,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨22,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨23,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨24,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨25,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨26,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨27,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨28,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨29,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨30,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨31,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨32,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨33,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨34,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨35,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨36,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨37,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨38,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨39,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨40,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨41,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨42,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨43,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨44,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨45,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨46,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨47,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨48,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨49,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨50,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨51,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12778) (by norm_num)
        (q := 1 - (cell12778 ⟨52,by decide⟩).lower)
        (by norm_num [cell12778]) (by norm_num [cell12778])
      exact ⟨E.1,E.2.trans (by norm_num [cell12778])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12778

/-! Source-cell containment and simple scalar guards at 12778. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12778)
open BstLean.Part268 (cell12778)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12778 ⟨10,by decide⟩).lower ∧ (cell12778 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12778 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12778 ⟨11,by decide⟩).lower ∧ (cell12778 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12778 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12778 ⟨12,by decide⟩).lower ∧ (cell12778 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12778 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12778 ⟨13,by decide⟩).lower ∧ (cell12778 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12778 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12778 ⟨14,by decide⟩).lower ∧ (cell12778 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12778 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12778 ⟨15,by decide⟩).lower ∧ (cell12778 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12778 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12778 ⟨16,by decide⟩).lower ∧ (cell12778 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12778 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12778 ⟨17,by decide⟩).lower ∧ (cell12778 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12778 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12778 ⟨18,by decide⟩).lower ∧ (cell12778 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12778 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12778 ⟨19,by decide⟩).lower ∧ (cell12778 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12778 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12778 ⟨20,by decide⟩).lower ∧ (cell12778 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12778 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12778 ⟨21,by decide⟩).lower ∧ (cell12778 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12778 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12778 ⟨22,by decide⟩).lower ∧ (cell12778 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12778 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12778 ⟨23,by decide⟩).lower ∧ (cell12778 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12778 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12778 ⟨24,by decide⟩).lower ∧ (cell12778 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12778 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12778 ⟨25,by decide⟩).lower ∧ (cell12778 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12778 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12778 ⟨26,by decide⟩).lower ∧ (cell12778 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12778 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12778 ⟨27,by decide⟩).lower ∧ (cell12778 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12778 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12778 ⟨28,by decide⟩).lower ∧ (cell12778 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12778 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12778 ⟨29,by decide⟩).lower ∧ (cell12778 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12778 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12778 ⟨30,by decide⟩).lower ∧ (cell12778 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12778 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12778 ⟨31,by decide⟩).lower ∧ (cell12778 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12778 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12778 ⟨32,by decide⟩).lower ∧ (cell12778 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12778 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12778 ⟨33,by decide⟩).lower ∧ (cell12778 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12778 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12778 ⟨34,by decide⟩).lower ∧ (cell12778 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12778 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12778 ⟨35,by decide⟩).lower ∧ (cell12778 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12778 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12778 ⟨36,by decide⟩).lower ∧ (cell12778 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12778 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12778 ⟨37,by decide⟩).lower ∧ (cell12778 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12778 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12778 ⟨38,by decide⟩).lower ∧ (cell12778 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12778 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12778 ⟨39,by decide⟩).lower ∧ (cell12778 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12778 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12778 ⟨40,by decide⟩).lower ∧ (cell12778 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12778 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12778 ⟨41,by decide⟩).lower ∧ (cell12778 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12778 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12778 ⟨42,by decide⟩).lower ∧ (cell12778 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12778 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12778 ⟨43,by decide⟩).lower ∧ (cell12778 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12778 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12778 ⟨44,by decide⟩).lower ∧ (cell12778 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12778 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12778 ⟨45,by decide⟩).lower ∧ (cell12778 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12778 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12778 ⟨46,by decide⟩).lower ∧ (cell12778 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12778 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12778 ⟨47,by decide⟩).lower ∧ (cell12778 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12778 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12778 ⟨48,by decide⟩).lower ∧ (cell12778 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12778 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12778 ⟨49,by decide⟩).lower ∧ (cell12778 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12778 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12778 ⟨50,by decide⟩).lower ∧ (cell12778 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12778 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12778 ⟨51,by decide⟩).lower ∧ (cell12778 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12778 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12778 ⟨52,by decide⟩).lower ∧ (cell12778 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12778 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12778 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12778 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12778,cell12778,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12778 i).lower ∧
    (cell12778 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12778 i).upper ≤ (0.532 : ℝ) ∧
    (cell12778 i).centre ≤ (0.1 : ℝ) ∧ (cell12778 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12778 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12778 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12778

/-! The local source numeric instances at 12778 have no network premises. -/
namespace BstLean.Part269.N12778
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12778)
open BstLean.Part268 (cell12778)

noncomputable def sourceNumerics12778 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12778 (cell12778 i)
      scalarRow12778.M scalarRow12778.H scalarRow12778.xi := by
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
    energy_allowance := scalarRow12778.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12778]
    centre_nonneg := (scalarRow12778.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12778])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12778
/-! Actual 12779 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12779 ≤ (1.035697390760 : ℝ) := by
  have hr : (113.044239127874 : ℝ) ≤ √(12779 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.044239127874 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12779 12779 (11 / 1000) ≤
    (0.008455866604 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12779) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.044239127874 : ℝ) ≤ √(12779 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12779)
  have hdiv : K / √(12779 : ℝ) ≤ K / 113.044239127874 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.044239127874 ≤ (0.008455866604 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12779.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12779 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12779 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12779 := gPlus_lower 12779
end BstLean.Part269.N12779

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12779
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035697390759 : ℝ) ≤ wn 12779 := by
  have hn : √(12779 : ℝ) ≤ 113.044239127875 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12779 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.044239127875 ≤ 2 / √(12779 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250296711 : ℝ) ≤ rhoBar 12779 BstLean.Part154.csC ∧
    rhoBar 12779 BstLean.Part154.csC ≤ 0.000250297099 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035697390759 : ℝ) / (1.295212 * 12779) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035697390760 : ℝ) / (1.29521 * 12779) := by gcongr
      _ ≤ (0.000250297099 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12779 BstLean.Part154.csC) ≤ 0.001001251045 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12779 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) ≤ 0.000191178557 ∧
    cc1 (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) ≤ 0.000121648197 ∧
    cc2 (rhoBar 12779 BstLean.Part154.csC) ≤ 0.000070617724 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12779 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12779 BstLean.Part154.csC * nuR (rhoBar 12779 BstLean.Part154.csC)) ≤ 0.000500609861 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250297099 : ℝ) * 0.001001251045 := by gcongr
      _ ≤ (0.000500609861 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12779 BstLean.Part154.csC) * nuR (rhoBar 12779 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001251045 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12779 BstLean.Part154.csC) * rhoBar 12779 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250297099 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250297099 / 2 + 0.399 * 0.001001251045 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191178557 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500609861 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121648197 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250297099 / 1.414213562 := by gcongr
      _ ≤ (0.000070617724 : ℝ) := by norm_num

end BstLean.Part269.N12779

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12779
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) ≤ 1.57839E-7 := by
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12779 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12779 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191178557 : ℝ) ^ 2 + 0.000121648197 ^ 2 + 3 * 0.000070617724 ^ 2 +
        2 * 0.797885 * 0.000191178557 * 0.000121648197 + 2 * 0.000191178557 * 0.000070617724 +
        4 * 0.797885 * 0.000121648197 * 0.000070617724 := by gcongr
    _ ≤ (1.57839E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12779 BstLean.Part154.csC Θ ≤ 0.002612474448 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12779 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12779 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035697390760 * 1.57839E-7 / (0.000250296711 : ℝ) := by gcongr
    _ ≤ 0.002612474448 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12779 BstLean.Part154.csC Θ ≤ 0.002898362878 + 0.000660129138 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12779 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035697390760 : ℝ) * ((2 * Θ * 0.000250297099 +
        (6863 / 10000) * 0.000250297099 * 12779 * 0.001001251045) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002898362878 + 0.000660129138 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12779 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12779 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12779 0.011 Θ ∧ gammaRatio 12779 0.011 Θ ≤ 0.000086045670 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12779 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035697390760 : ℝ) * 0.525 / ((1 - 0.011) * 12779) := by gcongr
      _ ≤ (0.000086045670 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12779 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12779 0.011 Θ) :=
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
    badAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12779 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12779 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12779 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12779 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12779 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12779 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12779 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12779 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12779 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12779 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035697390760 : ℝ) * 12779 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003458567437 + 0.003272603586 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12779

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12779
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12779 BstLean.Part154.csC) (piBar (rhoBar 12779 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12779 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12779 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12779 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12779 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12779 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12779 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12779 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12779 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12779 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052320075421 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12779) ≤ 0.010564338265 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12779 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035697390760)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010564338265 + 2 * 0.737676 / 12779) := by gcongr
    _ ≤ (0.052320075421 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12779 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12779

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12779
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507118819 : ℝ) ≤ plow 12779 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12779) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683284320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371549086) : eMP 12779 0.011 xi bn ≤ 0.001180883847 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12779 : ℝ) * (1 - 0.011))) ≤ 0.000583894060 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371549086 / (12779 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583894060 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583894060 : ℝ) + 3.141593 * 0.052683284320 / (12779 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180883847 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683284320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371549086) : PiBarMP 12779 12 0.011 xi bn ≤ 0.160746899069 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12779 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037034431088 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.420776549532 : ℝ) ≤ √((12779 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.044239127874 : ℝ) ≤ √(12779 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12779) ≤ 0.123247397393 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037034431088 + 0.052683284320 * 1.772454 / (2 * (112.420776549532 : ℝ))) * (1 + 0.001180883847) +
        8 / (12779 * 113.044239127874) + 0.123247397393 := by gcongr
    _ ≤ (0.160746899069 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683284320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371549086) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281848470876) :
    parallelOracle 12779 0.011 xi bn cd ≤ 0.161731279533 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12779 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12779 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507118819 : ℝ) ≤ plow 12779 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.044239127874 : ℝ) ≤ √(12779 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281848470876 : ℝ) / (2 * 0.560507118819 * 113.044239127874)) * 0.160746899069 +
        0.281848470876 ^ 2 / (2 * 0.560507118819 * 113.044239127874) := by gcongr
    _ ≤ (0.161731279533 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052683284320) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371549086)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281848470876) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12779 12779 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507118819 : ℝ) ≤ plow 12779 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.044239127874 : ℝ) ≤ √(12779 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12779 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12779 Θ 1.22 ≤ 0.011730810082 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.044239127874 := by gcongr <;> linarith
      _ ≤ (0.011730810082 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12779 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12779 12779 0.011 ≤ 0.008455866604 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12779 12779 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12779 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12779 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12779 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12779 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161731279533 + 0.011730810082 + (0.008455866604 : ℝ) *
        (1 + 2 * (0.281848470876 + 0.011730810082) / (0.560507118819 * 113.044239127874))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12779]

end BstLean.Part269.N12779

/-! The original eight local profiles supply actual 12779 moment certificates. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12779 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052683284320 ∧
    0 ≤ bN 12779 BstLean.Part154.csC (groupTheta g) ∧ bN 12779 BstLean.Part154.csC (groupTheta g) ≤ 0.001371549086 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12779 12779 0.011
      (momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12779 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12779 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12779 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229528395455 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12779 0.011
      (momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12779 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12779
/-! The actual computed-centre upper energy formula at 12779. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12779

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12779)
open BstLean.Part268 (cell12779)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085263163417
  | 2 => 0.086201814187
  | 3 => 0.087138018663
  | 4 => 0.088073059095
  | 5 => 0.089008490780
  | 6 => 0.089946183172
  | 7 => 0.090888364968
  | 8 => 0.091837673222
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12779 12779 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12779 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12779

/-! Actual upper energy certificates on all 43 source endpoints at 12779. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12779)
open BstLean.Part268 (cell12779)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12779 (gMinus 12779) (1 - (cell12779 i).lower) ≤ 1 ∧
    energyUpper 12779 (gMinus 12779) (BstLean.Part211.gPlus 12779)
      (finiteEnergy 12779 12779 0.011) (1 - (cell12779 i).lower) ≤
      (cell12779 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨10,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨11,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨12,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨13,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨14,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨15,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨16,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨17,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨18,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨19,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨20,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨21,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨22,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨23,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨24,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨25,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨26,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨27,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨28,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨29,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨30,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨31,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨32,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨33,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨34,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨35,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨36,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨37,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨38,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨39,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨40,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨41,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨42,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨43,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨44,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨45,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨46,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨47,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨48,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨49,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨50,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨51,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12779) (by norm_num)
        (q := 1 - (cell12779 ⟨52,by decide⟩).lower)
        (by norm_num [cell12779]) (by norm_num [cell12779])
      exact ⟨E.1,E.2.trans (by norm_num [cell12779])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12779

/-! Source-cell containment and simple scalar guards at 12779. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12779)
open BstLean.Part268 (cell12779)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12779 ⟨10,by decide⟩).lower ∧ (cell12779 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12779 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12779 ⟨11,by decide⟩).lower ∧ (cell12779 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12779 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12779 ⟨12,by decide⟩).lower ∧ (cell12779 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12779 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12779 ⟨13,by decide⟩).lower ∧ (cell12779 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12779 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12779 ⟨14,by decide⟩).lower ∧ (cell12779 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12779 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12779 ⟨15,by decide⟩).lower ∧ (cell12779 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12779 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12779 ⟨16,by decide⟩).lower ∧ (cell12779 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12779 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12779 ⟨17,by decide⟩).lower ∧ (cell12779 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12779 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12779 ⟨18,by decide⟩).lower ∧ (cell12779 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12779 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12779 ⟨19,by decide⟩).lower ∧ (cell12779 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12779 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12779 ⟨20,by decide⟩).lower ∧ (cell12779 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12779 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12779 ⟨21,by decide⟩).lower ∧ (cell12779 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12779 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12779 ⟨22,by decide⟩).lower ∧ (cell12779 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12779 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12779 ⟨23,by decide⟩).lower ∧ (cell12779 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12779 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12779 ⟨24,by decide⟩).lower ∧ (cell12779 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12779 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12779 ⟨25,by decide⟩).lower ∧ (cell12779 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12779 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12779 ⟨26,by decide⟩).lower ∧ (cell12779 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12779 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12779 ⟨27,by decide⟩).lower ∧ (cell12779 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12779 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12779 ⟨28,by decide⟩).lower ∧ (cell12779 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12779 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12779 ⟨29,by decide⟩).lower ∧ (cell12779 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12779 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12779 ⟨30,by decide⟩).lower ∧ (cell12779 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12779 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12779 ⟨31,by decide⟩).lower ∧ (cell12779 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12779 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12779 ⟨32,by decide⟩).lower ∧ (cell12779 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12779 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12779 ⟨33,by decide⟩).lower ∧ (cell12779 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12779 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12779 ⟨34,by decide⟩).lower ∧ (cell12779 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12779 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12779 ⟨35,by decide⟩).lower ∧ (cell12779 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12779 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12779 ⟨36,by decide⟩).lower ∧ (cell12779 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12779 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12779 ⟨37,by decide⟩).lower ∧ (cell12779 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12779 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12779 ⟨38,by decide⟩).lower ∧ (cell12779 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12779 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12779 ⟨39,by decide⟩).lower ∧ (cell12779 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12779 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12779 ⟨40,by decide⟩).lower ∧ (cell12779 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12779 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12779 ⟨41,by decide⟩).lower ∧ (cell12779 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12779 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12779 ⟨42,by decide⟩).lower ∧ (cell12779 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12779 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12779 ⟨43,by decide⟩).lower ∧ (cell12779 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12779 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12779 ⟨44,by decide⟩).lower ∧ (cell12779 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12779 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12779 ⟨45,by decide⟩).lower ∧ (cell12779 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12779 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12779 ⟨46,by decide⟩).lower ∧ (cell12779 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12779 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12779 ⟨47,by decide⟩).lower ∧ (cell12779 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12779 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12779 ⟨48,by decide⟩).lower ∧ (cell12779 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12779 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12779 ⟨49,by decide⟩).lower ∧ (cell12779 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12779 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12779 ⟨50,by decide⟩).lower ∧ (cell12779 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12779 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12779 ⟨51,by decide⟩).lower ∧ (cell12779 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12779 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12779 ⟨52,by decide⟩).lower ∧ (cell12779 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12779 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12779 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12779 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12779,cell12779,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12779 i).lower ∧
    (cell12779 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12779 i).upper ≤ (0.532 : ℝ) ∧
    (cell12779 i).centre ≤ (0.1 : ℝ) ∧ (cell12779 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12779 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12779 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12779

/-! The local source numeric instances at 12779 have no network premises. -/
namespace BstLean.Part269.N12779
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12779)
open BstLean.Part268 (cell12779)

noncomputable def sourceNumerics12779 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12779 (cell12779 i)
      scalarRow12779.M scalarRow12779.H scalarRow12779.xi := by
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
    energy_allowance := scalarRow12779.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12779]
    centre_nonneg := (scalarRow12779.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12779])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12779
/-! Actual 12780 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12780 ≤ (1.035695981875 : ℝ) := by
  have hr : (113.048662088500 : ℝ) ≤ √(12780 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.048662088500 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12780 12780 (11 / 1000) ≤
    (0.008455535771 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12780) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.048662088500 : ℝ) ≤ √(12780 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12780)
  have hdiv : K / √(12780 : ℝ) ≤ K / 113.048662088500 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.048662088500 ≤ (0.008455535771 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12780.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12780 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12780 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12780 := gPlus_lower 12780
end BstLean.Part269.N12780

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12780
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035695981874 : ℝ) ≤ wn 12780 := by
  have hn : √(12780 : ℝ) ≤ 113.048662088501 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12780 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.048662088501 ≤ 2 / √(12780 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250276786 : ℝ) ≤ rhoBar 12780 BstLean.Part154.csC ∧
    rhoBar 12780 BstLean.Part154.csC ≤ 0.000250277173 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035695981874 : ℝ) / (1.295212 * 12780) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035695981875 : ℝ) / (1.29521 * 12780) := by gcongr
      _ ≤ (0.000250277173 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12780 BstLean.Part154.csC) ≤ 0.001001171331 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12780 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) ≤ 0.000191163336 ∧
    cc1 (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) ≤ 0.000121638512 ∧
    cc2 (rhoBar 12780 BstLean.Part154.csC) ≤ 0.000070612102 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12780 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12780 BstLean.Part154.csC * nuR (rhoBar 12780 BstLean.Part154.csC)) ≤ 0.000500570006 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250277173 : ℝ) * 0.001001171331 := by gcongr
      _ ≤ (0.000500570006 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12780 BstLean.Part154.csC) * nuR (rhoBar 12780 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001171331 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12780 BstLean.Part154.csC) * rhoBar 12780 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250277173 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250277173 / 2 + 0.399 * 0.001001171331 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191163336 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500570006 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121638512 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250277173 / 1.414213562 := by gcongr
      _ ≤ (0.000070612102 : ℝ) := by norm_num

end BstLean.Part269.N12780

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12780
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) ≤ 1.57814E-7 := by
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12780 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12780 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191163336 : ℝ) ^ 2 + 0.000121638512 ^ 2 + 3 * 0.000070612102 ^ 2 +
        2 * 0.797885 * 0.000191163336 * 0.000121638512 + 2 * 0.000191163336 * 0.000070612102 +
        4 * 0.797885 * 0.000121638512 * 0.000070612102 := by gcongr
    _ ≤ (1.57814E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12780 BstLean.Part154.csC Θ ≤ 0.002612265058 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12780 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12780 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035695981875 * 1.57814E-7 / (0.000250276786 : ℝ) := by gcongr
    _ ≤ 0.002612265058 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12780 BstLean.Part154.csC Θ ≤ 0.002898124236 + 0.000660075688 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12780 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035695981875 : ℝ) * ((2 * Θ * 0.000250277173 +
        (6863 / 10000) * 0.000250277173 * 12780 * 0.001001171331) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002898124236 + 0.000660075688 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12780 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12780 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12780 0.011 Θ ∧ gammaRatio 12780 0.011 Θ ≤ 0.000086038820 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12780 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035695981875 : ℝ) * 0.525 / ((1 - 0.011) * 12780) := by gcongr
      _ ≤ (0.000086038820 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12780 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12780 0.011 Θ) :=
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
    badAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12780 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12780 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12780 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12780 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12780 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12780 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12780 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12780 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12780 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12780 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035695981875 : ℝ) * 12780 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003458328795 + 0.003272340746 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12780

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12780
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12780 BstLean.Part154.csC) (piBar (rhoBar 12780 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12780 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12780 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12780 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12780 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12780 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12780 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12780 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12780 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12780 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052318006304 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12780) ≤ 0.010563924942 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12780 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035695981875)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010563924942 + 2 * 0.737676 / 12780) := by gcongr
    _ ≤ (0.052318006304 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12780 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12780

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12780
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507163482 : ℝ) ≤ plow 12780 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12780) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682907687)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371439156) : eMP 12780 0.011 xi bn ≤ 0.001180790243 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12780 : ℝ) * (1 - 0.011))) ≤ 0.000583847817 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371439156 / (12780 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583847817 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583847817 : ℝ) + 3.141593 * 0.052682907687 / (12780 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180790243 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682907687)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371439156) : PiBarMP 12780 12 0.011 xi bn ≤ 0.160740567752 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12780 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037032946899 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.425175116608 : ℝ) ≤ √((12780 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.048662088500 : ℝ) ≤ √(12780 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12780) ≤ 0.123242575413 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037032946899 + 0.052682907687 * 1.772454 / (2 * (112.425175116608 : ℝ))) * (1 + 0.001180790243) +
        8 / (12780 * 113.048662088500) + 0.123242575413 := by gcongr
    _ ≤ (0.160740567752 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682907687)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371439156) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281845581308) :
    parallelOracle 12780 0.011 xi bn cd ≤ 0.161724879025 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12780 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12780 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507163482 : ℝ) ≤ plow 12780 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.048662088500 : ℝ) ≤ √(12780 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281845581308 : ℝ) / (2 * 0.560507163482 * 113.048662088500)) * 0.160740567752 +
        0.281845581308 ^ 2 / (2 * 0.560507163482 * 113.048662088500) := by gcongr
    _ ≤ (0.161724879025 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682907687) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371439156)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281845581308) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12780 12780 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507163482 : ℝ) ≤ plow 12780 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.048662088500 : ℝ) ≤ √(12780 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12780 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12780 Θ 1.22 ≤ 0.011730351121 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.048662088500 := by gcongr <;> linarith
      _ ≤ (0.011730351121 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12780 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12780 12780 0.011 ≤ 0.008455535771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12780 12780 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12780 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12780 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12780 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12780 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161724879025 + 0.011730351121 + (0.008455535771 : ℝ) *
        (1 + 2 * (0.281845581308 + 0.011730351121) / (0.560507163482 * 113.048662088500))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12780]

end BstLean.Part269.N12780

/-! The original eight local profiles supply actual 12780 moment certificates. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12780 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052682907687 ∧
    0 ≤ bN 12780 BstLean.Part154.csC (groupTheta g) ∧ bN 12780 BstLean.Part154.csC (groupTheta g) ≤ 0.001371439156 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12780 12780 0.011
      (momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12780 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12780 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12780 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229527575004 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12780 0.011
      (momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12780 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12780
/-! The actual computed-centre upper energy formula at 12780. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12780

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12780)
open BstLean.Part268 (cell12780)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085260329941
  | 2 => 0.086198930494
  | 3 => 0.087135077726
  | 4 => 0.088070052250
  | 5 => 0.089005407430
  | 6 => 0.089943010458
  | 7 => 0.090885087400
  | 8 => 0.091834272268
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12780 12780 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12780 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12780

/-! Actual upper energy certificates on all 43 source endpoints at 12780. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12780)
open BstLean.Part268 (cell12780)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12780 (gMinus 12780) (1 - (cell12780 i).lower) ≤ 1 ∧
    energyUpper 12780 (gMinus 12780) (BstLean.Part211.gPlus 12780)
      (finiteEnergy 12780 12780 0.011) (1 - (cell12780 i).lower) ≤
      (cell12780 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨10,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨11,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨12,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨13,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨14,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨15,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨16,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨17,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨18,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨19,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨20,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨21,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨22,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨23,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨24,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨25,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨26,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨27,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨28,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨29,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨30,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨31,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨32,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨33,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨34,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨35,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨36,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨37,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨38,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨39,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨40,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨41,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨42,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨43,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨44,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨45,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨46,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨47,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨48,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨49,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨50,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨51,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12780) (by norm_num)
        (q := 1 - (cell12780 ⟨52,by decide⟩).lower)
        (by norm_num [cell12780]) (by norm_num [cell12780])
      exact ⟨E.1,E.2.trans (by norm_num [cell12780])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12780

/-! Source-cell containment and simple scalar guards at 12780. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12780)
open BstLean.Part268 (cell12780)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12780 ⟨10,by decide⟩).lower ∧ (cell12780 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12780 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12780 ⟨11,by decide⟩).lower ∧ (cell12780 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12780 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12780 ⟨12,by decide⟩).lower ∧ (cell12780 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12780 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12780 ⟨13,by decide⟩).lower ∧ (cell12780 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12780 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12780 ⟨14,by decide⟩).lower ∧ (cell12780 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12780 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12780 ⟨15,by decide⟩).lower ∧ (cell12780 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12780 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12780 ⟨16,by decide⟩).lower ∧ (cell12780 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12780 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12780 ⟨17,by decide⟩).lower ∧ (cell12780 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12780 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12780 ⟨18,by decide⟩).lower ∧ (cell12780 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12780 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12780 ⟨19,by decide⟩).lower ∧ (cell12780 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12780 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12780 ⟨20,by decide⟩).lower ∧ (cell12780 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12780 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12780 ⟨21,by decide⟩).lower ∧ (cell12780 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12780 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12780 ⟨22,by decide⟩).lower ∧ (cell12780 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12780 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12780 ⟨23,by decide⟩).lower ∧ (cell12780 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12780 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12780 ⟨24,by decide⟩).lower ∧ (cell12780 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12780 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12780 ⟨25,by decide⟩).lower ∧ (cell12780 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12780 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12780 ⟨26,by decide⟩).lower ∧ (cell12780 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12780 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12780 ⟨27,by decide⟩).lower ∧ (cell12780 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12780 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12780 ⟨28,by decide⟩).lower ∧ (cell12780 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12780 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12780 ⟨29,by decide⟩).lower ∧ (cell12780 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12780 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12780 ⟨30,by decide⟩).lower ∧ (cell12780 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12780 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12780 ⟨31,by decide⟩).lower ∧ (cell12780 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12780 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12780 ⟨32,by decide⟩).lower ∧ (cell12780 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12780 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12780 ⟨33,by decide⟩).lower ∧ (cell12780 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12780 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12780 ⟨34,by decide⟩).lower ∧ (cell12780 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12780 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12780 ⟨35,by decide⟩).lower ∧ (cell12780 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12780 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12780 ⟨36,by decide⟩).lower ∧ (cell12780 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12780 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12780 ⟨37,by decide⟩).lower ∧ (cell12780 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12780 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12780 ⟨38,by decide⟩).lower ∧ (cell12780 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12780 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12780 ⟨39,by decide⟩).lower ∧ (cell12780 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12780 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12780 ⟨40,by decide⟩).lower ∧ (cell12780 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12780 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12780 ⟨41,by decide⟩).lower ∧ (cell12780 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12780 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12780 ⟨42,by decide⟩).lower ∧ (cell12780 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12780 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12780 ⟨43,by decide⟩).lower ∧ (cell12780 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12780 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12780 ⟨44,by decide⟩).lower ∧ (cell12780 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12780 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12780 ⟨45,by decide⟩).lower ∧ (cell12780 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12780 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12780 ⟨46,by decide⟩).lower ∧ (cell12780 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12780 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12780 ⟨47,by decide⟩).lower ∧ (cell12780 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12780 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12780 ⟨48,by decide⟩).lower ∧ (cell12780 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12780 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12780 ⟨49,by decide⟩).lower ∧ (cell12780 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12780 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12780 ⟨50,by decide⟩).lower ∧ (cell12780 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12780 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12780 ⟨51,by decide⟩).lower ∧ (cell12780 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12780 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12780 ⟨52,by decide⟩).lower ∧ (cell12780 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12780 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12780 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12780 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12780,cell12780,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12780 i).lower ∧
    (cell12780 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12780 i).upper ≤ (0.532 : ℝ) ∧
    (cell12780 i).centre ≤ (0.1 : ℝ) ∧ (cell12780 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12780 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12780 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12780

/-! The local source numeric instances at 12780 have no network premises. -/
namespace BstLean.Part269.N12780
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12780)
open BstLean.Part268 (cell12780)

noncomputable def sourceNumerics12780 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12780 (cell12780 i)
      scalarRow12780.M scalarRow12780.H scalarRow12780.xi := by
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
    energy_allowance := scalarRow12780.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12780]
    centre_nonneg := (scalarRow12780.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12780])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12780
/-! Actual 12781 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12781 ≤ (1.035694573156 : ℝ) := by
  have hr : (113.053084876088 : ℝ) ≤ √(12781 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.053084876088 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12781 12781 (11 / 1000) ≤
    (0.008455204976 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12781) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.053084876088 : ℝ) ≤ √(12781 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12781)
  have hdiv : K / √(12781 : ℝ) ≤ K / 113.053084876088 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.053084876088 ≤ (0.008455204976 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12781.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12781 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12781 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12781 := gPlus_lower 12781
end BstLean.Part269.N12781

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12781
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035694573155 : ℝ) ≤ wn 12781 := by
  have hn : √(12781 : ℝ) ≤ 113.053084876089 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12781 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.053084876089 ≤ 2 / √(12781 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250256863 : ℝ) ≤ rhoBar 12781 BstLean.Part154.csC ∧
    rhoBar 12781 BstLean.Part154.csC ≤ 0.000250257251 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035694573155 : ℝ) / (1.295212 * 12781) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035694573156 : ℝ) / (1.29521 * 12781) := by gcongr
      _ ≤ (0.000250257251 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12781 BstLean.Part154.csC) ≤ 0.001001091633 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12781 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) ≤ 0.000191148119 ∧
    cc1 (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) ≤ 0.000121628829 ∧
    cc2 (rhoBar 12781 BstLean.Part154.csC) ≤ 0.000070606482 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12781 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12781 BstLean.Part154.csC * nuR (rhoBar 12781 BstLean.Part154.csC)) ≤ 0.000500530160 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250257251 : ℝ) * 0.001001091633 := by gcongr
      _ ≤ (0.000500530160 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12781 BstLean.Part154.csC) * nuR (rhoBar 12781 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001091633 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12781 BstLean.Part154.csC) * rhoBar 12781 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250257251 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250257251 / 2 + 0.399 * 0.001001091633 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191148119 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500530160 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121628829 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250257251 / 1.414213562 := by gcongr
      _ ≤ (0.000070606482 : ℝ) := by norm_num

end BstLean.Part269.N12781

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12781
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) ≤ 1.57789E-7 := by
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12781 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12781 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191148119 : ℝ) ^ 2 + 0.000121628829 ^ 2 + 3 * 0.000070606482 ^ 2 +
        2 * 0.797885 * 0.000191148119 * 0.000121628829 + 2 * 0.000191148119 * 0.000070606482 +
        4 * 0.797885 * 0.000121628829 * 0.000070606482 := by gcongr
    _ ≤ (1.57789E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12781 BstLean.Part154.csC Θ ≤ 0.002612055615 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12781 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12781 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035694573156 * 1.57789E-7 / (0.000250256863 : ℝ) := by gcongr
    _ ≤ 0.002612055615 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12781 BstLean.Part154.csC Θ ≤ 0.002897885653 + 0.000660022248 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12781 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035694573156 : ℝ) * ((2 * Θ * 0.000250257251 +
        (6863 / 10000) * 0.000250257251 * 12781 * 0.001001091633) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002897885653 + 0.000660022248 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12781 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12781 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12781 0.011 Θ ∧ gammaRatio 12781 0.011 Θ ≤ 0.000086031972 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12781 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035694573156 : ℝ) * 0.525 / ((1 - 0.011) * 12781) := by gcongr
      _ ≤ (0.000086031972 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12781 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12781 0.011 Θ) :=
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
    badAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12781 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12781 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12781 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12781 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12781 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12781 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12781 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12781 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12781 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12781 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035694573156 : ℝ) * 12781 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003458090212 + 0.003272077863 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12781

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12781
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12781 BstLean.Part154.csC) (piBar (rhoBar 12781 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12781 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12781 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12781 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12781 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12781 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12781 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12781 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12781 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12781 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052315937429 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12781) ≤ 0.010563511667 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12781 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035694573156)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010563511667 + 2 * 0.737676 / 12781) := by gcongr
    _ ≤ (0.052315937429 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12781 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12781

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12781
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507208137 : ℝ) ≤ plow 12781 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12781) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682531091)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371329198) : eMP 12781 0.011 xi bn ≤ 0.001180696631 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12781 : ℝ) * (1 - 0.011))) ≤ 0.000583801570 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371329198 / (12781 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583801570 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583801570 : ℝ) + 3.141593 * 0.052682531091 / (12781 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180696631 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682531091)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371329198) : PiBarMP 12781 12 0.011 xi bn ≤ 0.160734236564 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12781 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037031462272 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.429573511598 : ℝ) ≤ √((12781 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.053084876088 : ℝ) ≤ √(12781 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12781) ≤ 0.123237753999 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037031462272 + 0.052682531091 * 1.772454 / (2 * (112.429573511598 : ℝ))) * (1 + 0.001180696631) +
        8 / (12781 * 113.053084876088) + 0.123237753999 := by gcongr
    _ ≤ (0.160734236564 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682531091)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371329198) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281842692060) :
    parallelOracle 12781 0.011 xi bn cd ≤ 0.161718478656 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12781 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12781 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507208137 : ℝ) ≤ plow 12781 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.053084876088 : ℝ) ≤ √(12781 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281842692060 : ℝ) / (2 * 0.560507208137 * 113.053084876088)) * 0.160734236564 +
        0.281842692060 ^ 2 / (2 * 0.560507208137 * 113.053084876088) := by gcongr
    _ ≤ (0.161718478656 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682531091) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371329198)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281842692060) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12781 12781 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507208137 : ℝ) ≤ plow 12781 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.053084876088 : ℝ) ≤ √(12781 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12781 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12781 Θ 1.22 ≤ 0.011729892214 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.053084876088 := by gcongr <;> linarith
      _ ≤ (0.011729892214 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12781 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12781 12781 0.011 ≤ 0.008455204976 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12781 12781 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12781 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12781 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12781 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12781 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161718478656 + 0.011729892214 + (0.008455204976 : ℝ) *
        (1 + 2 * (0.281842692060 + 0.011729892214) / (0.560507208137 * 113.053084876088))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12781]

end BstLean.Part269.N12781

/-! The original eight local profiles supply actual 12781 moment certificates. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12781 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052682531091 ∧
    0 ≤ bN 12781 BstLean.Part154.csC (groupTheta g) ∧ bN 12781 BstLean.Part154.csC (groupTheta g) ≤ 0.001371329198 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12781 12781 0.011
      (momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12781 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12781 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12781 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229526754631 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12781 0.011
      (momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12781 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12781
/-! The actual computed-centre upper energy formula at 12781. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12781

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12781)
open BstLean.Part268 (cell12781)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085257497467
  | 2 => 0.086196047842
  | 3 => 0.087132137880
  | 4 => 0.088067046557
  | 5 => 0.089002325306
  | 6 => 0.089939839060
  | 7 => 0.090881811258
  | 8 => 0.091830872873
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12781 12781 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12781 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12781

/-! Actual upper energy certificates on all 43 source endpoints at 12781. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12781)
open BstLean.Part268 (cell12781)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12781 (gMinus 12781) (1 - (cell12781 i).lower) ≤ 1 ∧
    energyUpper 12781 (gMinus 12781) (BstLean.Part211.gPlus 12781)
      (finiteEnergy 12781 12781 0.011) (1 - (cell12781 i).lower) ≤
      (cell12781 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨10,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨11,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨12,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨13,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨14,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨15,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨16,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨17,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨18,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨19,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨20,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨21,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨22,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨23,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨24,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨25,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨26,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨27,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨28,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨29,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨30,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨31,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨32,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨33,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨34,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨35,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨36,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨37,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨38,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨39,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨40,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨41,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨42,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨43,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨44,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨45,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨46,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨47,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨48,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨49,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨50,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨51,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12781) (by norm_num)
        (q := 1 - (cell12781 ⟨52,by decide⟩).lower)
        (by norm_num [cell12781]) (by norm_num [cell12781])
      exact ⟨E.1,E.2.trans (by norm_num [cell12781])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12781

/-! Source-cell containment and simple scalar guards at 12781. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12781)
open BstLean.Part268 (cell12781)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12781 ⟨10,by decide⟩).lower ∧ (cell12781 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12781 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12781 ⟨11,by decide⟩).lower ∧ (cell12781 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12781 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12781 ⟨12,by decide⟩).lower ∧ (cell12781 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12781 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12781 ⟨13,by decide⟩).lower ∧ (cell12781 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12781 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12781 ⟨14,by decide⟩).lower ∧ (cell12781 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12781 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12781 ⟨15,by decide⟩).lower ∧ (cell12781 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12781 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12781 ⟨16,by decide⟩).lower ∧ (cell12781 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12781 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12781 ⟨17,by decide⟩).lower ∧ (cell12781 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12781 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12781 ⟨18,by decide⟩).lower ∧ (cell12781 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12781 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12781 ⟨19,by decide⟩).lower ∧ (cell12781 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12781 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12781 ⟨20,by decide⟩).lower ∧ (cell12781 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12781 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12781 ⟨21,by decide⟩).lower ∧ (cell12781 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12781 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12781 ⟨22,by decide⟩).lower ∧ (cell12781 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12781 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12781 ⟨23,by decide⟩).lower ∧ (cell12781 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12781 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12781 ⟨24,by decide⟩).lower ∧ (cell12781 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12781 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12781 ⟨25,by decide⟩).lower ∧ (cell12781 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12781 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12781 ⟨26,by decide⟩).lower ∧ (cell12781 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12781 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12781 ⟨27,by decide⟩).lower ∧ (cell12781 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12781 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12781 ⟨28,by decide⟩).lower ∧ (cell12781 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12781 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12781 ⟨29,by decide⟩).lower ∧ (cell12781 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12781 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12781 ⟨30,by decide⟩).lower ∧ (cell12781 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12781 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12781 ⟨31,by decide⟩).lower ∧ (cell12781 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12781 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12781 ⟨32,by decide⟩).lower ∧ (cell12781 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12781 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12781 ⟨33,by decide⟩).lower ∧ (cell12781 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12781 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12781 ⟨34,by decide⟩).lower ∧ (cell12781 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12781 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12781 ⟨35,by decide⟩).lower ∧ (cell12781 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12781 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12781 ⟨36,by decide⟩).lower ∧ (cell12781 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12781 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12781 ⟨37,by decide⟩).lower ∧ (cell12781 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12781 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12781 ⟨38,by decide⟩).lower ∧ (cell12781 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12781 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12781 ⟨39,by decide⟩).lower ∧ (cell12781 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12781 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12781 ⟨40,by decide⟩).lower ∧ (cell12781 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12781 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12781 ⟨41,by decide⟩).lower ∧ (cell12781 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12781 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12781 ⟨42,by decide⟩).lower ∧ (cell12781 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12781 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12781 ⟨43,by decide⟩).lower ∧ (cell12781 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12781 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12781 ⟨44,by decide⟩).lower ∧ (cell12781 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12781 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12781 ⟨45,by decide⟩).lower ∧ (cell12781 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12781 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12781 ⟨46,by decide⟩).lower ∧ (cell12781 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12781 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12781 ⟨47,by decide⟩).lower ∧ (cell12781 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12781 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12781 ⟨48,by decide⟩).lower ∧ (cell12781 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12781 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12781 ⟨49,by decide⟩).lower ∧ (cell12781 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12781 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12781 ⟨50,by decide⟩).lower ∧ (cell12781 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12781 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12781 ⟨51,by decide⟩).lower ∧ (cell12781 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12781 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12781 ⟨52,by decide⟩).lower ∧ (cell12781 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12781 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12781 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12781 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12781,cell12781,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12781 i).lower ∧
    (cell12781 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12781 i).upper ≤ (0.532 : ℝ) ∧
    (cell12781 i).centre ≤ (0.1 : ℝ) ∧ (cell12781 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12781 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12781 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12781

/-! The local source numeric instances at 12781 have no network premises. -/
namespace BstLean.Part269.N12781
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12781)
open BstLean.Part268 (cell12781)

noncomputable def sourceNumerics12781 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12781 (cell12781 i)
      scalarRow12781.M scalarRow12781.H scalarRow12781.xi := by
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
    energy_allowance := scalarRow12781.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12781]
    centre_nonneg := (scalarRow12781.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12781])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12781
/-! Actual 12782 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12782 ≤ (1.035693164604 : ℝ) := by
  have hr : (113.057507490657 : ℝ) ≤ √(12782 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.057507490657 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12782 12782 (11 / 1000) ≤
    (0.008454874221 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12782) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.057507490657 : ℝ) ≤ √(12782 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12782)
  have hdiv : K / √(12782 : ℝ) ≤ K / 113.057507490657 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.057507490657 ≤ (0.008454874221 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12782.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12782 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12782 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12782 := gPlus_lower 12782
end BstLean.Part269.N12782

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12782
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035693164603 : ℝ) ≤ wn 12782 := by
  have hn : √(12782 : ℝ) ≤ 113.057507490658 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12782 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.057507490658 ≤ 2 / √(12782 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250236944 : ℝ) ≤ rhoBar 12782 BstLean.Part154.csC ∧
    rhoBar 12782 BstLean.Part154.csC ≤ 0.000250237331 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035693164603 : ℝ) / (1.295212 * 12782) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035693164604 : ℝ) / (1.29521 * 12782) := by gcongr
      _ ≤ (0.000250237331 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12782 BstLean.Part154.csC) ≤ 0.001001011943 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12782 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) ≤ 0.000191132903 ∧
    cc1 (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) ≤ 0.000121619148 ∧
    cc2 (rhoBar 12782 BstLean.Part154.csC) ≤ 0.000070600861 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12782 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12782 BstLean.Part154.csC * nuR (rhoBar 12782 BstLean.Part154.csC)) ≤ 0.000500490317 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250237331 : ℝ) * 0.001001011943 := by gcongr
      _ ≤ (0.000500490317 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12782 BstLean.Part154.csC) * nuR (rhoBar 12782 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001011943 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12782 BstLean.Part154.csC) * rhoBar 12782 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250237331 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250237331 / 2 + 0.399 * 0.001001011943 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191132903 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500490317 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121619148 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250237331 / 1.414213562 := by gcongr
      _ ≤ (0.000070600861 : ℝ) := by norm_num

end BstLean.Part269.N12782

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12782
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) ≤ 1.57763E-7 := by
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12782 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12782 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191132903 : ℝ) ^ 2 + 0.000121619148 ^ 2 + 3 * 0.000070600861 ^ 2 +
        2 * 0.797885 * 0.000191132903 * 0.000121619148 + 2 * 0.000191132903 * 0.000070600861 +
        4 * 0.797885 * 0.000121619148 * 0.000070600861 := by gcongr
    _ ≤ (1.57763E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12782 BstLean.Part154.csC Θ ≤ 0.002611829543 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12782 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12782 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035693164604 * 1.57763E-7 / (0.000250236944 : ℝ) := by gcongr
    _ ≤ 0.002611829543 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12782 BstLean.Part154.csC Θ ≤ 0.002897647081 + 0.000659968814 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12782 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035693164604 : ℝ) * ((2 * Θ * 0.000250237331 +
        (6863 / 10000) * 0.000250237331 * 12782 * 0.001001011943) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002897647081 + 0.000659968814 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12782 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12782 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12782 0.011 Θ ∧ gammaRatio 12782 0.011 Θ ≤ 0.000086025124 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12782 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035693164604 : ℝ) * 0.525 / ((1 - 0.011) * 12782) := by gcongr
      _ ≤ (0.000086025124 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12782 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12782 0.011 Θ) :=
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
    badAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12782 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12782 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12782 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12782 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12782 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12782 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12782 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12782 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12782 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12782 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035693164604 : ℝ) * 12782 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003457851640 + 0.003271798357 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12782

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12782
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12782 BstLean.Part154.csC) (piBar (rhoBar 12782 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12782 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12782 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12782 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12782 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12782 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12782 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12782 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12782 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12782 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052313868801 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12782) ≤ 0.010563098441 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12782 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035693164604)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010563098441 + 2 * 0.737676 / 12782) := by gcongr
    _ ≤ (0.052313868801 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12782 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12782

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12782
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507252785 : ℝ) ≤ plow 12782 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12782) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682145778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371210511) : eMP 12782 0.011 xi bn ≤ 0.001180599311 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12782 : ℝ) * (1 - 0.011))) ≤ 0.000583753470 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371210511 / (12782 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583753470 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583753470 : ℝ) + 3.141593 * 0.052682145778 / (12782 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180599311 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682145778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371210511) : PiBarMP 12782 12 0.011 xi bn ≤ 0.160727787676 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12782 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037029859722 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.433971734525 : ℝ) ≤ √((12782 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.057507490657 : ℝ) ≤ √(12782 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12782) ≤ 0.123232933151 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037029859722 + 0.052682145778 * 1.772454 / (2 * (112.433971734525 : ℝ))) * (1 + 0.001180599311) +
        8 / (12782 * 113.057507490657) + 0.123232933151 := by gcongr
    _ ≤ (0.160727787676 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682145778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371210511) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281839784066) :
    parallelOracle 12782 0.011 xi bn cd ≤ 0.161711960225 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12782 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12782 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507252785 : ℝ) ≤ plow 12782 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.057507490657 : ℝ) ≤ √(12782 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281839784066 : ℝ) / (2 * 0.560507252785 * 113.057507490657)) * 0.160727787676 +
        0.281839784066 ^ 2 / (2 * 0.560507252785 * 113.057507490657) := by gcongr
    _ ≤ (0.161711960225 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052682145778) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371210511)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281839784066) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12782 12782 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507252785 : ℝ) ≤ plow 12782 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.057507490657 : ℝ) ≤ √(12782 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12782 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12782 Θ 1.22 ≤ 0.011729433361 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.057507490657 := by gcongr <;> linarith
      _ ≤ (0.011729433361 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12782 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12782 12782 0.011 ≤ 0.008454874221 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12782 12782 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12782 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12782 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12782 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12782 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161711960225 + 0.011729433361 + (0.008454874221 : ℝ) *
        (1 + 2 * (0.281839784066 + 0.011729433361) / (0.560507252785 * 113.057507490657))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12782]

end BstLean.Part269.N12782

/-! The original eight local profiles supply actual 12782 moment certificates. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12782 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052682145778 ∧
    0 ≤ bN 12782 BstLean.Part154.csC (groupTheta g) ∧ bN 12782 BstLean.Part154.csC (groupTheta g) ≤ 0.001371210511 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12782 12782 0.011
      (momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12782 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12782 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12782 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229525915265 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12782 0.011
      (momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12782 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12782
/-! The actual computed-centre upper energy formula at 12782. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12782

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12782)
open BstLean.Part268 (cell12782)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085254665992
  | 2 => 0.086193166230
  | 3 => 0.087129199123
  | 4 => 0.088064042013
  | 5 => 0.088999244406
  | 6 => 0.089936668977
  | 7 => 0.090878536540
  | 8 => 0.091827475034
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12782 12782 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12782 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12782

/-! Actual upper energy certificates on all 43 source endpoints at 12782. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12782)
open BstLean.Part268 (cell12782)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12782 (gMinus 12782) (1 - (cell12782 i).lower) ≤ 1 ∧
    energyUpper 12782 (gMinus 12782) (BstLean.Part211.gPlus 12782)
      (finiteEnergy 12782 12782 0.011) (1 - (cell12782 i).lower) ≤
      (cell12782 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨10,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨11,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨12,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨13,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨14,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨15,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨16,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨17,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨18,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨19,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨20,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨21,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨22,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨23,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨24,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨25,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨26,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨27,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨28,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨29,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨30,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨31,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨32,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨33,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨34,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨35,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨36,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨37,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨38,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨39,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨40,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨41,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨42,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨43,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨44,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨45,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨46,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨47,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨48,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨49,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨50,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨51,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12782) (by norm_num)
        (q := 1 - (cell12782 ⟨52,by decide⟩).lower)
        (by norm_num [cell12782]) (by norm_num [cell12782])
      exact ⟨E.1,E.2.trans (by norm_num [cell12782])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12782

/-! Source-cell containment and simple scalar guards at 12782. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12782)
open BstLean.Part268 (cell12782)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12782 ⟨10,by decide⟩).lower ∧ (cell12782 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12782 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12782 ⟨11,by decide⟩).lower ∧ (cell12782 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12782 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12782 ⟨12,by decide⟩).lower ∧ (cell12782 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12782 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12782 ⟨13,by decide⟩).lower ∧ (cell12782 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12782 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12782 ⟨14,by decide⟩).lower ∧ (cell12782 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12782 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12782 ⟨15,by decide⟩).lower ∧ (cell12782 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12782 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12782 ⟨16,by decide⟩).lower ∧ (cell12782 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12782 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12782 ⟨17,by decide⟩).lower ∧ (cell12782 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12782 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12782 ⟨18,by decide⟩).lower ∧ (cell12782 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12782 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12782 ⟨19,by decide⟩).lower ∧ (cell12782 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12782 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12782 ⟨20,by decide⟩).lower ∧ (cell12782 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12782 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12782 ⟨21,by decide⟩).lower ∧ (cell12782 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12782 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12782 ⟨22,by decide⟩).lower ∧ (cell12782 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12782 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12782 ⟨23,by decide⟩).lower ∧ (cell12782 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12782 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12782 ⟨24,by decide⟩).lower ∧ (cell12782 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12782 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12782 ⟨25,by decide⟩).lower ∧ (cell12782 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12782 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12782 ⟨26,by decide⟩).lower ∧ (cell12782 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12782 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12782 ⟨27,by decide⟩).lower ∧ (cell12782 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12782 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12782 ⟨28,by decide⟩).lower ∧ (cell12782 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12782 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12782 ⟨29,by decide⟩).lower ∧ (cell12782 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12782 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12782 ⟨30,by decide⟩).lower ∧ (cell12782 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12782 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12782 ⟨31,by decide⟩).lower ∧ (cell12782 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12782 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12782 ⟨32,by decide⟩).lower ∧ (cell12782 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12782 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12782 ⟨33,by decide⟩).lower ∧ (cell12782 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12782 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12782 ⟨34,by decide⟩).lower ∧ (cell12782 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12782 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12782 ⟨35,by decide⟩).lower ∧ (cell12782 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12782 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12782 ⟨36,by decide⟩).lower ∧ (cell12782 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12782 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12782 ⟨37,by decide⟩).lower ∧ (cell12782 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12782 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12782 ⟨38,by decide⟩).lower ∧ (cell12782 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12782 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12782 ⟨39,by decide⟩).lower ∧ (cell12782 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12782 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12782 ⟨40,by decide⟩).lower ∧ (cell12782 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12782 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12782 ⟨41,by decide⟩).lower ∧ (cell12782 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12782 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12782 ⟨42,by decide⟩).lower ∧ (cell12782 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12782 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12782 ⟨43,by decide⟩).lower ∧ (cell12782 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12782 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12782 ⟨44,by decide⟩).lower ∧ (cell12782 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12782 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12782 ⟨45,by decide⟩).lower ∧ (cell12782 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12782 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12782 ⟨46,by decide⟩).lower ∧ (cell12782 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12782 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12782 ⟨47,by decide⟩).lower ∧ (cell12782 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12782 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12782 ⟨48,by decide⟩).lower ∧ (cell12782 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12782 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12782 ⟨49,by decide⟩).lower ∧ (cell12782 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12782 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12782 ⟨50,by decide⟩).lower ∧ (cell12782 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12782 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12782 ⟨51,by decide⟩).lower ∧ (cell12782 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12782 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12782 ⟨52,by decide⟩).lower ∧ (cell12782 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12782 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12782 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12782 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12782,cell12782,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12782 i).lower ∧
    (cell12782 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12782 i).upper ≤ (0.532 : ℝ) ∧
    (cell12782 i).centre ≤ (0.1 : ℝ) ∧ (cell12782 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12782 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12782 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12782

/-! The local source numeric instances at 12782 have no network premises. -/
namespace BstLean.Part269.N12782
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12782)
open BstLean.Part268 (cell12782)

noncomputable def sourceNumerics12782 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12782 (cell12782 i)
      scalarRow12782.M scalarRow12782.H scalarRow12782.xi := by
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
    energy_allowance := scalarRow12782.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12782]
    centre_nonneg := (scalarRow12782.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12782])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12782
/-! Actual 12783 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12783 ≤ (1.035691756218 : ℝ) := by
  have hr : (113.061929932227 : ℝ) ≤ √(12783 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.061929932227 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12783 12783 (11 / 1000) ≤
    (0.008454543504 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12783) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.061929932227 : ℝ) ≤ √(12783 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12783)
  have hdiv : K / √(12783 : ℝ) ≤ K / 113.061929932227 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.061929932227 ≤ (0.008454543504 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12783.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12783 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12783 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12783 := gPlus_lower 12783
end BstLean.Part269.N12783

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12783
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035691756217 : ℝ) ≤ wn 12783 := by
  have hn : √(12783 : ℝ) ≤ 113.061929932228 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12783 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.061929932228 ≤ 2 / √(12783 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250217028 : ℝ) ≤ rhoBar 12783 BstLean.Part154.csC ∧
    rhoBar 12783 BstLean.Part154.csC ≤ 0.000250217415 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035691756217 : ℝ) / (1.295212 * 12783) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035691756218 : ℝ) / (1.29521 * 12783) := by gcongr
      _ ≤ (0.000250217415 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12783 BstLean.Part154.csC) ≤ 0.001000932269 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12783 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) ≤ 0.000191117691 ∧
    cc1 (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) ≤ 0.000121609468 ∧
    cc2 (rhoBar 12783 BstLean.Part154.csC) ≤ 0.000070595242 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12783 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12783 BstLean.Part154.csC * nuR (rhoBar 12783 BstLean.Part154.csC)) ≤ 0.000500450483 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250217415 : ℝ) * 0.001000932269 := by gcongr
      _ ≤ (0.000500450483 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12783 BstLean.Part154.csC) * nuR (rhoBar 12783 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000932269 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12783 BstLean.Part154.csC) * rhoBar 12783 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250217415 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250217415 / 2 + 0.399 * 0.001000932269 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191117691 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500450483 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121609468 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250217415 / 1.414213562 := by gcongr
      _ ≤ (0.000070595242 : ℝ) := by norm_num

end BstLean.Part269.N12783

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12783
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) ≤ 1.57738E-7 := by
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12783 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12783 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191117691 : ℝ) ^ 2 + 0.000121609468 ^ 2 + 3 * 0.000070595242 ^ 2 +
        2 * 0.797885 * 0.000191117691 * 0.000121609468 + 2 * 0.000191117691 * 0.000070595242 +
        4 * 0.797885 * 0.000121609468 * 0.000070595242 := by gcongr
    _ ≤ (1.57738E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12783 BstLean.Part154.csC Θ ≤ 0.002611619962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12783 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12783 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035691756218 * 1.57738E-7 / (0.000250217028 : ℝ) := by gcongr
    _ ≤ 0.002611619962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12783 BstLean.Part154.csC Θ ≤ 0.002897408568 + 0.000659915391 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12783 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035691756218 : ℝ) * ((2 * Θ * 0.000250217415 +
        (6863 / 10000) * 0.000250217415 * 12783 * 0.001000932269) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002897408568 + 0.000659915391 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12783 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12783 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12783 0.011 Θ ∧ gammaRatio 12783 0.011 Θ ≤ 0.000086018277 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12783 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035691756218 : ℝ) * 0.525 / ((1 - 0.011) * 12783) := by gcongr
      _ ≤ (0.000086018277 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12783 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12783 0.011 Θ) :=
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
    badAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12783 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12783 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12783 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12783 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12783 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12783 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12783 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12783 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12783 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12783 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035691756218 : ℝ) * 12783 *
        (2.0559E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003457613127 + 0.003271535353 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12783

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12783
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12783 BstLean.Part154.csC) (piBar (rhoBar 12783 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12783 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12783 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12783 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12783 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12783 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12783 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12783 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12783 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12783 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052311800414 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12783) ≤ 0.010562685263 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12783 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035691756218)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010562685263 + 2 * 0.737676 / 12783) := by gcongr
    _ ≤ (0.052311800414 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12783 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12783

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12783
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507297426 : ℝ) ≤ plow 12783 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12783) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681769188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371100481) : eMP 12783 0.011 xi bn ≤ 0.001180505685 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12783 : ℝ) * (1 - 0.011))) ≤ 0.000583707216 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001371100481 / (12783 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583707216 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583707216 : ℝ) + 3.141593 * 0.052681769188 / (12783 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180505685 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681769188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371100481) : PiBarMP 12783 12 0.011 xi bn ≤ 0.160721456527 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12783 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037028373999 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.438369785407 : ℝ) ≤ √((12783 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.061929932227 : ℝ) ≤ √(12783 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12783) ≤ 0.123228112868 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037028373999 + 0.052681769188 * 1.772454 / (2 * (112.438369785407 : ℝ))) * (1 + 0.001180505685) +
        8 / (12783 * 113.061929932227) + 0.123228112868 := by gcongr
    _ ≤ (0.160721456527 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681769188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371100481) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281836895313) :
    parallelOracle 12783 0.011 xi bn cd ≤ 0.161705559913 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12783 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12783 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507297426 : ℝ) ≤ plow 12783 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.061929932227 : ℝ) ≤ √(12783 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281836895313 : ℝ) / (2 * 0.560507297426 * 113.061929932227)) * 0.160721456527 +
        0.281836895313 ^ 2 / (2 * 0.560507297426 * 113.061929932227) := by gcongr
    _ ≤ (0.161705559913 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681769188) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001371100481)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281836895313) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12783 12783 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507297426 : ℝ) ≤ plow 12783 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.061929932227 : ℝ) ≤ √(12783 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12783 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12783 Θ 1.22 ≤ 0.011728974562 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.061929932227 := by gcongr <;> linarith
      _ ≤ (0.011728974562 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12783 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12783 12783 0.011 ≤ 0.008454543504 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12783 12783 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12783 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12783 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12783 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12783 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161705559913 + 0.011728974562 + (0.008454543504 : ℝ) *
        (1 + 2 * (0.281836895313 + 0.011728974562) / (0.560507297426 * 113.061929932227))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12783]

end BstLean.Part269.N12783

/-! The original eight local profiles supply actual 12783 moment certificates. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12783 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052681769188 ∧
    0 ≤ bN 12783 BstLean.Part154.csC (groupTheta g) ∧ bN 12783 BstLean.Part154.csC (groupTheta g) ≤ 0.001371100481 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12783 12783 0.011
      (momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12783 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12783 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12783 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229525094899 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12783 0.011
      (momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12783 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12783
/-! The actual computed-centre upper energy formula at 12783. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12783

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12783)
open BstLean.Part268 (cell12783)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085251835515
  | 2 => 0.086190285656
  | 3 => 0.087126261454
  | 4 => 0.088061038618
  | 5 => 0.088996164729
  | 6 => 0.089933500208
  | 7 => 0.090875263246
  | 8 => 0.091824078750
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12783 12783 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12783 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12783

/-! Actual upper energy certificates on all 43 source endpoints at 12783. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12783)
open BstLean.Part268 (cell12783)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12783 (gMinus 12783) (1 - (cell12783 i).lower) ≤ 1 ∧
    energyUpper 12783 (gMinus 12783) (BstLean.Part211.gPlus 12783)
      (finiteEnergy 12783 12783 0.011) (1 - (cell12783 i).lower) ≤
      (cell12783 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨10,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨11,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨12,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨13,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨14,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨15,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨16,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨17,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨18,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨19,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨20,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨21,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨22,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨23,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨24,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨25,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨26,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨27,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨28,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨29,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨30,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨31,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨32,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨33,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨34,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨35,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨36,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨37,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨38,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨39,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨40,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨41,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨42,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨43,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨44,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨45,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨46,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨47,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨48,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨49,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨50,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨51,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12783) (by norm_num)
        (q := 1 - (cell12783 ⟨52,by decide⟩).lower)
        (by norm_num [cell12783]) (by norm_num [cell12783])
      exact ⟨E.1,E.2.trans (by norm_num [cell12783])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12783

/-! Source-cell containment and simple scalar guards at 12783. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12783)
open BstLean.Part268 (cell12783)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12783 ⟨10,by decide⟩).lower ∧ (cell12783 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12783 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12783 ⟨11,by decide⟩).lower ∧ (cell12783 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12783 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12783 ⟨12,by decide⟩).lower ∧ (cell12783 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12783 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12783 ⟨13,by decide⟩).lower ∧ (cell12783 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12783 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12783 ⟨14,by decide⟩).lower ∧ (cell12783 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12783 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12783 ⟨15,by decide⟩).lower ∧ (cell12783 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12783 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12783 ⟨16,by decide⟩).lower ∧ (cell12783 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12783 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12783 ⟨17,by decide⟩).lower ∧ (cell12783 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12783 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12783 ⟨18,by decide⟩).lower ∧ (cell12783 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12783 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12783 ⟨19,by decide⟩).lower ∧ (cell12783 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12783 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12783 ⟨20,by decide⟩).lower ∧ (cell12783 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12783 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12783 ⟨21,by decide⟩).lower ∧ (cell12783 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12783 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12783 ⟨22,by decide⟩).lower ∧ (cell12783 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12783 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12783 ⟨23,by decide⟩).lower ∧ (cell12783 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12783 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12783 ⟨24,by decide⟩).lower ∧ (cell12783 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12783 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12783 ⟨25,by decide⟩).lower ∧ (cell12783 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12783 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12783 ⟨26,by decide⟩).lower ∧ (cell12783 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12783 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12783 ⟨27,by decide⟩).lower ∧ (cell12783 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12783 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12783 ⟨28,by decide⟩).lower ∧ (cell12783 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12783 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12783 ⟨29,by decide⟩).lower ∧ (cell12783 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12783 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12783 ⟨30,by decide⟩).lower ∧ (cell12783 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12783 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12783 ⟨31,by decide⟩).lower ∧ (cell12783 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12783 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12783 ⟨32,by decide⟩).lower ∧ (cell12783 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12783 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12783 ⟨33,by decide⟩).lower ∧ (cell12783 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12783 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12783 ⟨34,by decide⟩).lower ∧ (cell12783 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12783 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12783 ⟨35,by decide⟩).lower ∧ (cell12783 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12783 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12783 ⟨36,by decide⟩).lower ∧ (cell12783 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12783 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12783 ⟨37,by decide⟩).lower ∧ (cell12783 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12783 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12783 ⟨38,by decide⟩).lower ∧ (cell12783 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12783 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12783 ⟨39,by decide⟩).lower ∧ (cell12783 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12783 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12783 ⟨40,by decide⟩).lower ∧ (cell12783 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12783 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12783 ⟨41,by decide⟩).lower ∧ (cell12783 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12783 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12783 ⟨42,by decide⟩).lower ∧ (cell12783 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12783 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12783 ⟨43,by decide⟩).lower ∧ (cell12783 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12783 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12783 ⟨44,by decide⟩).lower ∧ (cell12783 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12783 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12783 ⟨45,by decide⟩).lower ∧ (cell12783 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12783 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12783 ⟨46,by decide⟩).lower ∧ (cell12783 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12783 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12783 ⟨47,by decide⟩).lower ∧ (cell12783 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12783 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12783 ⟨48,by decide⟩).lower ∧ (cell12783 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12783 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12783 ⟨49,by decide⟩).lower ∧ (cell12783 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12783 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12783 ⟨50,by decide⟩).lower ∧ (cell12783 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12783 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12783 ⟨51,by decide⟩).lower ∧ (cell12783 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12783 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12783 ⟨52,by decide⟩).lower ∧ (cell12783 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12783 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12783 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12783 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12783,cell12783,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12783 i).lower ∧
    (cell12783 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12783 i).upper ≤ (0.532 : ℝ) ∧
    (cell12783 i).centre ≤ (0.1 : ℝ) ∧ (cell12783 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12783 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12783 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12783

/-! The local source numeric instances at 12783 have no network premises. -/
namespace BstLean.Part269.N12783
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12783)
open BstLean.Part268 (cell12783)

noncomputable def sourceNumerics12783 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12783 (cell12783 i)
      scalarRow12783.M scalarRow12783.H scalarRow12783.xi := by
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
    energy_allowance := scalarRow12783.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12783]
    centre_nonneg := (scalarRow12783.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12783])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12783
/-! Actual 12784 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12784 ≤ (1.035690347998 : ℝ) := by
  have hr : (113.066352200820 : ℝ) ≤ √(12784 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.066352200820 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12784 12784 (11 / 1000) ≤
    (0.008454212826 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12784) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.066352200820 : ℝ) ≤ √(12784 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12784)
  have hdiv : K / √(12784 : ℝ) ≤ K / 113.066352200820 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.066352200820 ≤ (0.008454212826 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12784.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12784 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12784 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12784 := gPlus_lower 12784
end BstLean.Part269.N12784

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12784
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035690347997 : ℝ) ≤ wn 12784 := by
  have hn : √(12784 : ℝ) ≤ 113.066352200821 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12784 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.066352200821 ≤ 2 / √(12784 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250197115 : ℝ) ≤ rhoBar 12784 BstLean.Part154.csC ∧
    rhoBar 12784 BstLean.Part154.csC ≤ 0.000250197503 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035690347997 : ℝ) / (1.295212 * 12784) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035690347998 : ℝ) / (1.29521 * 12784) := by gcongr
      _ ≤ (0.000250197503 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12784 BstLean.Part154.csC) ≤ 0.001000852611 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12784 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) ≤ 0.000191102481 ∧
    cc1 (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) ≤ 0.000121599790 ∧
    cc2 (rhoBar 12784 BstLean.Part154.csC) ≤ 0.000070589625 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12784 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12784 BstLean.Part154.csC * nuR (rhoBar 12784 BstLean.Part154.csC)) ≤ 0.000500410656 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250197503 : ℝ) * 0.001000852611 := by gcongr
      _ ≤ (0.000500410656 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12784 BstLean.Part154.csC) * nuR (rhoBar 12784 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000852611 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12784 BstLean.Part154.csC) * rhoBar 12784 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250197503 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250197503 / 2 + 0.399 * 0.001000852611 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191102481 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500410656 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121599790 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250197503 / 1.414213562 := by gcongr
      _ ≤ (0.000070589625 : ℝ) := by norm_num

end BstLean.Part269.N12784

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12784
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) ≤ 1.57713E-7 := by
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12784 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12784 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191102481 : ℝ) ^ 2 + 0.000121599790 ^ 2 + 3 * 0.000070589625 ^ 2 +
        2 * 0.797885 * 0.000191102481 * 0.000121599790 + 2 * 0.000191102481 * 0.000070589625 +
        4 * 0.797885 * 0.000121599790 * 0.000070589625 := by gcongr
    _ ≤ (1.57713E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12784 BstLean.Part154.csC Θ ≤ 0.002611410318 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12784 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12784 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035690347998 * 1.57713E-7 / (0.000250197115 : ℝ) := by gcongr
    _ ≤ 0.002611410318 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12784 BstLean.Part154.csC Θ ≤ 0.002897170113 + 0.000659861979 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12784 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035690347998 : ℝ) * ((2 * Θ * 0.000250197503 +
        (6863 / 10000) * 0.000250197503 * 12784 * 0.001000852611) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002897170113 + 0.000659861979 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12784 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12784 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12784 0.011 Θ ∧ gammaRatio 12784 0.011 Θ ≤ 0.000086011432 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12784 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035690347998 : ℝ) * 0.525 / ((1 - 0.011) * 12784) := by gcongr
      _ ≤ (0.000086011432 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12784 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12784 0.011 Θ) :=
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
    badAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12784 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12784 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12784 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12784 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12784 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12784 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12784 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12784 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12784 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12784 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035690347998 : ℝ) * 12784 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003457374672 + 0.003271272297 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12784

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12784
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12784 BstLean.Part154.csC) (piBar (rhoBar 12784 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12784 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12784 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12784 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12784 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12784 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12784 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12784 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12784 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12784 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052309732275 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12784) ≤ 0.010562272134 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12784 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035690347998)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010562272134 + 2 * 0.737676 / 12784) := by gcongr
    _ ≤ (0.052309732275 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12784 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12784

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12784
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507342060 : ℝ) ≤ plow 12784 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12784) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681392628)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370990417) : eMP 12784 0.011 xi bn ≤ 0.001180412051 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12784 : ℝ) * (1 - 0.011))) ≤ 0.000583660958 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370990417 / (12784 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583660958 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583660958 : ℝ) + 3.141593 * 0.052681392628 / (12784 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180412051 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681392628)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370990417) : PiBarMP 12784 12 0.011 xi bn ≤ 0.160715125428 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12784 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037026887758 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.442767664265 : ℝ) ≤ √((12784 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.066352200820 : ℝ) ≤ √(12784 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12784) ≤ 0.123223293151 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037026887758 + 0.052681392628 * 1.772454 / (2 * (112.442767664265 : ℝ))) * (1 + 0.001180412051) +
        8 / (12784 * 113.066352200820) + 0.123223293151 := by gcongr
    _ ≤ (0.160715125428 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681392628)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370990417) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281834006870) :
    parallelOracle 12784 0.011 xi bn cd ≤ 0.161699159660 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12784 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12784 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507342060 : ℝ) ≤ plow 12784 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.066352200820 : ℝ) ≤ √(12784 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281834006870 : ℝ) / (2 * 0.560507342060 * 113.066352200820)) * 0.160715125428 +
        0.281834006870 ^ 2 / (2 * 0.560507342060 * 113.066352200820) := by gcongr
    _ ≤ (0.161699159660 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681392628) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370990417)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281834006870) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12784 12784 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507342060 : ℝ) ≤ plow 12784 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.066352200820 : ℝ) ≤ √(12784 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12784 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12784 Θ 1.22 ≤ 0.011728515816 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.066352200820 := by gcongr <;> linarith
      _ ≤ (0.011728515816 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12784 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12784 12784 0.011 ≤ 0.008454212826 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12784 12784 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12784 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12784 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12784 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12784 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161699159660 + 0.011728515816 + (0.008454212826 : ℝ) *
        (1 + 2 * (0.281834006870 + 0.011728515816) / (0.560507342060 * 113.066352200820))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12784]

end BstLean.Part269.N12784

/-! The original eight local profiles supply actual 12784 moment certificates. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12784 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052681392628 ∧
    0 ≤ bN 12784 BstLean.Part154.csC (groupTheta g) ∧ bN 12784 BstLean.Part154.csC (groupTheta g) ≤ 0.001370990417 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12784 12784 0.011
      (momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12784 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12784 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12784 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229524274595 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12784 0.011
      (momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12784 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12784
/-! The actual computed-centre upper energy formula at 12784. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12784

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12784)
open BstLean.Part268 (cell12784)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085249006036
  | 2 => 0.086187406119
  | 3 => 0.087123324872
  | 4 => 0.088058036370
  | 5 => 0.088993086273
  | 6 => 0.089930332751
  | 7 => 0.090871991374
  | 8 => 0.091820684020
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12784 12784 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12784 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12784

/-! Actual upper energy certificates on all 43 source endpoints at 12784. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12784)
open BstLean.Part268 (cell12784)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12784 (gMinus 12784) (1 - (cell12784 i).lower) ≤ 1 ∧
    energyUpper 12784 (gMinus 12784) (BstLean.Part211.gPlus 12784)
      (finiteEnergy 12784 12784 0.011) (1 - (cell12784 i).lower) ≤
      (cell12784 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨10,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨11,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨12,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨13,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨14,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨15,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨16,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨17,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨18,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨19,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨20,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨21,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨22,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨23,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨24,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨25,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨26,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨27,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨28,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨29,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨30,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨31,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨32,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨33,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨34,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨35,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨36,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨37,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨38,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨39,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨40,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨41,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨42,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨43,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨44,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨45,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨46,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨47,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨48,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨49,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨50,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨51,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12784) (by norm_num)
        (q := 1 - (cell12784 ⟨52,by decide⟩).lower)
        (by norm_num [cell12784]) (by norm_num [cell12784])
      exact ⟨E.1,E.2.trans (by norm_num [cell12784])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12784

/-! Source-cell containment and simple scalar guards at 12784. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12784)
open BstLean.Part268 (cell12784)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12784 ⟨10,by decide⟩).lower ∧ (cell12784 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12784 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12784 ⟨11,by decide⟩).lower ∧ (cell12784 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12784 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12784 ⟨12,by decide⟩).lower ∧ (cell12784 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12784 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12784 ⟨13,by decide⟩).lower ∧ (cell12784 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12784 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12784 ⟨14,by decide⟩).lower ∧ (cell12784 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12784 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12784 ⟨15,by decide⟩).lower ∧ (cell12784 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12784 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12784 ⟨16,by decide⟩).lower ∧ (cell12784 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12784 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12784 ⟨17,by decide⟩).lower ∧ (cell12784 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12784 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12784 ⟨18,by decide⟩).lower ∧ (cell12784 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12784 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12784 ⟨19,by decide⟩).lower ∧ (cell12784 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12784 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12784 ⟨20,by decide⟩).lower ∧ (cell12784 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12784 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12784 ⟨21,by decide⟩).lower ∧ (cell12784 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12784 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12784 ⟨22,by decide⟩).lower ∧ (cell12784 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12784 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12784 ⟨23,by decide⟩).lower ∧ (cell12784 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12784 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12784 ⟨24,by decide⟩).lower ∧ (cell12784 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12784 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12784 ⟨25,by decide⟩).lower ∧ (cell12784 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12784 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12784 ⟨26,by decide⟩).lower ∧ (cell12784 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12784 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12784 ⟨27,by decide⟩).lower ∧ (cell12784 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12784 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12784 ⟨28,by decide⟩).lower ∧ (cell12784 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12784 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12784 ⟨29,by decide⟩).lower ∧ (cell12784 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12784 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12784 ⟨30,by decide⟩).lower ∧ (cell12784 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12784 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12784 ⟨31,by decide⟩).lower ∧ (cell12784 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12784 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12784 ⟨32,by decide⟩).lower ∧ (cell12784 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12784 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12784 ⟨33,by decide⟩).lower ∧ (cell12784 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12784 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12784 ⟨34,by decide⟩).lower ∧ (cell12784 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12784 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12784 ⟨35,by decide⟩).lower ∧ (cell12784 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12784 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12784 ⟨36,by decide⟩).lower ∧ (cell12784 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12784 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12784 ⟨37,by decide⟩).lower ∧ (cell12784 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12784 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12784 ⟨38,by decide⟩).lower ∧ (cell12784 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12784 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12784 ⟨39,by decide⟩).lower ∧ (cell12784 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12784 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12784 ⟨40,by decide⟩).lower ∧ (cell12784 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12784 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12784 ⟨41,by decide⟩).lower ∧ (cell12784 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12784 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12784 ⟨42,by decide⟩).lower ∧ (cell12784 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12784 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12784 ⟨43,by decide⟩).lower ∧ (cell12784 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12784 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12784 ⟨44,by decide⟩).lower ∧ (cell12784 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12784 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12784 ⟨45,by decide⟩).lower ∧ (cell12784 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12784 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12784 ⟨46,by decide⟩).lower ∧ (cell12784 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12784 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12784 ⟨47,by decide⟩).lower ∧ (cell12784 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12784 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12784 ⟨48,by decide⟩).lower ∧ (cell12784 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12784 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12784 ⟨49,by decide⟩).lower ∧ (cell12784 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12784 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12784 ⟨50,by decide⟩).lower ∧ (cell12784 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12784 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12784 ⟨51,by decide⟩).lower ∧ (cell12784 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12784 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12784 ⟨52,by decide⟩).lower ∧ (cell12784 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12784 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12784 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12784 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12784,cell12784,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12784 i).lower ∧
    (cell12784 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12784 i).upper ≤ (0.532 : ℝ) ∧
    (cell12784 i).centre ≤ (0.1 : ℝ) ∧ (cell12784 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12784 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12784 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12784

/-! The local source numeric instances at 12784 have no network premises. -/
namespace BstLean.Part269.N12784
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12784)
open BstLean.Part268 (cell12784)

noncomputable def sourceNumerics12784 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12784 (cell12784 i)
      scalarRow12784.M scalarRow12784.H scalarRow12784.xi := by
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
    energy_allowance := scalarRow12784.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12784]
    centre_nonneg := (scalarRow12784.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12784])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12784
/-! Actual 12785 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12785 ≤ (1.035688939945 : ℝ) := by
  have hr : (113.070774296455 : ℝ) ≤ √(12785 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.070774296455 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12785 12785 (11 / 1000) ≤
    (0.008453882187 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12785) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.070774296455 : ℝ) ≤ √(12785 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12785)
  have hdiv : K / √(12785 : ℝ) ≤ K / 113.070774296455 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.070774296455 ≤ (0.008453882187 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12785.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12785 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12785 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12785 := gPlus_lower 12785
end BstLean.Part269.N12785

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12785
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035688939944 : ℝ) ≤ wn 12785 := by
  have hn : √(12785 : ℝ) ≤ 113.070774296456 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12785 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.070774296456 ≤ 2 / √(12785 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250177206 : ℝ) ≤ rhoBar 12785 BstLean.Part154.csC ∧
    rhoBar 12785 BstLean.Part154.csC ≤ 0.000250177593 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035688939944 : ℝ) / (1.295212 * 12785) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035688939945 : ℝ) / (1.29521 * 12785) := by gcongr
      _ ≤ (0.000250177593 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12785 BstLean.Part154.csC) ≤ 0.001000772961 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12785 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) ≤ 0.000191087273 ∧
    cc1 (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) ≤ 0.000121590113 ∧
    cc2 (rhoBar 12785 BstLean.Part154.csC) ≤ 0.000070584007 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12785 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12785 BstLean.Part154.csC * nuR (rhoBar 12785 BstLean.Part154.csC)) ≤ 0.000500370834 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250177593 : ℝ) * 0.001000772961 := by gcongr
      _ ≤ (0.000500370834 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12785 BstLean.Part154.csC) * nuR (rhoBar 12785 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000772961 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12785 BstLean.Part154.csC) * rhoBar 12785 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250177593 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250177593 / 2 + 0.399 * 0.001000772961 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191087273 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500370834 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121590113 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250177593 / 1.414213562 := by gcongr
      _ ≤ (0.000070584007 : ℝ) := by norm_num

end BstLean.Part269.N12785

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12785
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) ≤ 1.57688E-7 := by
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12785 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12785 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191087273 : ℝ) ^ 2 + 0.000121590113 ^ 2 + 3 * 0.000070584007 ^ 2 +
        2 * 0.797885 * 0.000191087273 * 0.000121590113 + 2 * 0.000191087273 * 0.000070584007 +
        4 * 0.797885 * 0.000121590113 * 0.000070584007 := by gcongr
    _ ≤ (1.57688E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12785 BstLean.Part154.csC Θ ≤ 0.002611200600 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12785 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12785 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035688939945 * 1.57688E-7 / (0.000250177206 : ℝ) := by gcongr
    _ ≤ 0.002611200600 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12785 BstLean.Part154.csC Θ ≤ 0.002896931670 + 0.000659808572 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12785 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035688939945 : ℝ) * ((2 * Θ * 0.000250177593 +
        (6863 / 10000) * 0.000250177593 * 12785 * 0.001000772961) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002896931670 + 0.000659808572 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12785 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12785 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12785 0.011 Θ ∧ gammaRatio 12785 0.011 Θ ≤ 0.000086004587 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12785 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035688939945 : ℝ) * 0.525 / ((1 - 0.011) * 12785) := by gcongr
      _ ≤ (0.000086004587 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12785 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12785 0.011 Θ) :=
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
    badAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12785 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12785 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12785 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12785 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12785 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12785 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12785 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12785 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12785 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12785 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035688939945 : ℝ) * 12785 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003457136229 + 0.003271009172 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12785

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12785
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12785 BstLean.Part154.csC) (piBar (rhoBar 12785 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12785 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12785 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12785 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12785 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12785 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12785 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12785 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12785 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12785 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052307664378 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12785) ≤ 0.010561859053 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12785 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035688939945)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010561859053 + 2 * 0.737676 / 12785) := by gcongr
    _ ≤ (0.052307664378 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12785 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12785

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12785
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507386687 : ℝ) ≤ plow 12785 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12785) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681016045)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370880315) : eMP 12785 0.011 xi bn ≤ 0.001180318408 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12785 : ℝ) * (1 - 0.011))) ≤ 0.000583614695 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370880315 / (12785 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583614695 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583614695 : ℝ) + 3.141593 * 0.052681016045 / (12785 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180318408 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681016045)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370880315) : PiBarMP 12785 12 0.011 xi bn ≤ 0.160708794323 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12785 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037025400944 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.447165371119 : ℝ) ≤ √((12785 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.070774296455 : ℝ) ≤ √(12785 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12785) ≤ 0.123218474000 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037025400944 + 0.052681016045 * 1.772454 / (2 * (112.447165371119 : ℝ))) * (1 + 0.001180318408) +
        8 / (12785 * 113.070774296455) + 0.123218474000 := by gcongr
    _ ≤ (0.160708794323 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681016045)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370880315) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281831118616) :
    parallelOracle 12785 0.011 xi bn cd ≤ 0.161692759409 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12785 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12785 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507386687 : ℝ) ≤ plow 12785 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.070774296455 : ℝ) ≤ √(12785 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281831118616 : ℝ) / (2 * 0.560507386687 * 113.070774296455)) * 0.160708794323 +
        0.281831118616 ^ 2 / (2 * 0.560507386687 * 113.070774296455) := by gcongr
    _ ≤ (0.161692759409 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052681016045) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370880315)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281831118616) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12785 12785 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507386687 : ℝ) ≤ plow 12785 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.070774296455 : ℝ) ≤ √(12785 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12785 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12785 Θ 1.22 ≤ 0.011728057124 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.070774296455 := by gcongr <;> linarith
      _ ≤ (0.011728057124 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12785 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12785 12785 0.011 ≤ 0.008453882187 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12785 12785 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12785 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12785 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12785 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12785 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161692759409 + 0.011728057124 + (0.008453882187 : ℝ) *
        (1 + 2 * (0.281831118616 + 0.011728057124) / (0.560507386687 * 113.070774296455))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12785]

end BstLean.Part269.N12785

/-! The original eight local profiles supply actual 12785 moment certificates. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12785 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052681016045 ∧
    0 ≤ bN 12785 BstLean.Part154.csC (groupTheta g) ∧ bN 12785 BstLean.Part154.csC (groupTheta g) ≤ 0.001370880315 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12785 12785 0.011
      (momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12785 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12785 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12785 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229523454238 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12785 0.011
      (momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12785 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12785
/-! The actual computed-centre upper energy formula at 12785. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12785

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12785)
open BstLean.Part268 (cell12785)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085246177553
  | 2 => 0.086184527619
  | 3 => 0.087120389375
  | 4 => 0.088055035269
  | 5 => 0.088990009039
  | 6 => 0.089927166605
  | 7 => 0.090868720922
  | 8 => 0.091817290842
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12785 12785 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12785 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12785

/-! Actual upper energy certificates on all 43 source endpoints at 12785. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12785)
open BstLean.Part268 (cell12785)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12785 (gMinus 12785) (1 - (cell12785 i).lower) ≤ 1 ∧
    energyUpper 12785 (gMinus 12785) (BstLean.Part211.gPlus 12785)
      (finiteEnergy 12785 12785 0.011) (1 - (cell12785 i).lower) ≤
      (cell12785 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨10,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨11,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨12,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨13,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨14,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨15,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨16,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨17,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨18,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨19,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨20,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨21,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨22,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨23,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨24,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨25,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨26,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨27,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨28,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨29,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨30,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨31,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨32,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨33,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨34,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨35,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨36,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨37,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨38,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨39,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨40,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨41,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨42,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨43,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨44,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨45,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨46,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨47,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨48,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨49,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨50,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨51,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12785) (by norm_num)
        (q := 1 - (cell12785 ⟨52,by decide⟩).lower)
        (by norm_num [cell12785]) (by norm_num [cell12785])
      exact ⟨E.1,E.2.trans (by norm_num [cell12785])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12785

/-! Source-cell containment and simple scalar guards at 12785. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12785)
open BstLean.Part268 (cell12785)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12785 ⟨10,by decide⟩).lower ∧ (cell12785 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12785 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12785 ⟨11,by decide⟩).lower ∧ (cell12785 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12785 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12785 ⟨12,by decide⟩).lower ∧ (cell12785 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12785 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12785 ⟨13,by decide⟩).lower ∧ (cell12785 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12785 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12785 ⟨14,by decide⟩).lower ∧ (cell12785 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12785 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12785 ⟨15,by decide⟩).lower ∧ (cell12785 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12785 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12785 ⟨16,by decide⟩).lower ∧ (cell12785 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12785 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12785 ⟨17,by decide⟩).lower ∧ (cell12785 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12785 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12785 ⟨18,by decide⟩).lower ∧ (cell12785 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12785 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12785 ⟨19,by decide⟩).lower ∧ (cell12785 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12785 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12785 ⟨20,by decide⟩).lower ∧ (cell12785 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12785 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12785 ⟨21,by decide⟩).lower ∧ (cell12785 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12785 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12785 ⟨22,by decide⟩).lower ∧ (cell12785 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12785 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12785 ⟨23,by decide⟩).lower ∧ (cell12785 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12785 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12785 ⟨24,by decide⟩).lower ∧ (cell12785 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12785 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12785 ⟨25,by decide⟩).lower ∧ (cell12785 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12785 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12785 ⟨26,by decide⟩).lower ∧ (cell12785 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12785 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12785 ⟨27,by decide⟩).lower ∧ (cell12785 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12785 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12785 ⟨28,by decide⟩).lower ∧ (cell12785 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12785 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12785 ⟨29,by decide⟩).lower ∧ (cell12785 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12785 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12785 ⟨30,by decide⟩).lower ∧ (cell12785 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12785 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12785 ⟨31,by decide⟩).lower ∧ (cell12785 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12785 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12785 ⟨32,by decide⟩).lower ∧ (cell12785 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12785 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12785 ⟨33,by decide⟩).lower ∧ (cell12785 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12785 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12785 ⟨34,by decide⟩).lower ∧ (cell12785 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12785 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12785 ⟨35,by decide⟩).lower ∧ (cell12785 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12785 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12785 ⟨36,by decide⟩).lower ∧ (cell12785 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12785 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12785 ⟨37,by decide⟩).lower ∧ (cell12785 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12785 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12785 ⟨38,by decide⟩).lower ∧ (cell12785 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12785 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12785 ⟨39,by decide⟩).lower ∧ (cell12785 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12785 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12785 ⟨40,by decide⟩).lower ∧ (cell12785 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12785 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12785 ⟨41,by decide⟩).lower ∧ (cell12785 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12785 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12785 ⟨42,by decide⟩).lower ∧ (cell12785 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12785 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12785 ⟨43,by decide⟩).lower ∧ (cell12785 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12785 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12785 ⟨44,by decide⟩).lower ∧ (cell12785 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12785 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12785 ⟨45,by decide⟩).lower ∧ (cell12785 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12785 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12785 ⟨46,by decide⟩).lower ∧ (cell12785 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12785 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12785 ⟨47,by decide⟩).lower ∧ (cell12785 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12785 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12785 ⟨48,by decide⟩).lower ∧ (cell12785 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12785 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12785 ⟨49,by decide⟩).lower ∧ (cell12785 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12785 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12785 ⟨50,by decide⟩).lower ∧ (cell12785 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12785 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12785 ⟨51,by decide⟩).lower ∧ (cell12785 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12785 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12785 ⟨52,by decide⟩).lower ∧ (cell12785 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12785 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12785 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12785 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12785,cell12785,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12785 i).lower ∧
    (cell12785 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12785 i).upper ≤ (0.532 : ℝ) ∧
    (cell12785 i).centre ≤ (0.1 : ℝ) ∧ (cell12785 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12785 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12785 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12785

/-! The local source numeric instances at 12785 have no network premises. -/
namespace BstLean.Part269.N12785
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12785)
open BstLean.Part268 (cell12785)

noncomputable def sourceNumerics12785 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12785 (cell12785 i)
      scalarRow12785.M scalarRow12785.H scalarRow12785.xi := by
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
    energy_allowance := scalarRow12785.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12785]
    centre_nonneg := (scalarRow12785.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12785])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12785
/-! Actual 12786 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12786 ≤ (1.035687532057 : ℝ) := by
  have hr : (113.075196219153 : ℝ) ≤ √(12786 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.075196219153 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12786 12786 (11 / 1000) ≤
    (0.008453551587 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12786) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.075196219153 : ℝ) ≤ √(12786 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12786)
  have hdiv : K / √(12786 : ℝ) ≤ K / 113.075196219153 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.075196219153 ≤ (0.008453551587 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12786.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12786 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12786 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12786 := gPlus_lower 12786
end BstLean.Part269.N12786

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12786
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035687532056 : ℝ) ≤ wn 12786 := by
  have hn : √(12786 : ℝ) ≤ 113.075196219154 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12786 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.075196219154 ≤ 2 / √(12786 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250157299 : ℝ) ≤ rhoBar 12786 BstLean.Part154.csC ∧
    rhoBar 12786 BstLean.Part154.csC ≤ 0.000250157686 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035687532056 : ℝ) / (1.295212 * 12786) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035687532057 : ℝ) / (1.29521 * 12786) := by gcongr
      _ ≤ (0.000250157686 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12786 BstLean.Part154.csC) ≤ 0.001000693323 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12786 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) ≤ 0.000191072067 ∧
    cc1 (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) ≤ 0.000121580438 ∧
    cc2 (rhoBar 12786 BstLean.Part154.csC) ≤ 0.000070578391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12786 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12786 BstLean.Part154.csC * nuR (rhoBar 12786 BstLean.Part154.csC)) ≤ 0.000500331017 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250157686 : ℝ) * 0.001000693323 := by gcongr
      _ ≤ (0.000500331017 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12786 BstLean.Part154.csC) * nuR (rhoBar 12786 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000693323 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12786 BstLean.Part154.csC) * rhoBar 12786 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250157686 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250157686 / 2 + 0.399 * 0.001000693323 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191072067 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500331017 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121580438 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250157686 / 1.414213562 := by gcongr
      _ ≤ (0.000070578391 : ℝ) := by norm_num

end BstLean.Part269.N12786

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12786
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) ≤ 1.57663E-7 := by
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12786 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12786 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191072067 : ℝ) ^ 2 + 0.000121580438 ^ 2 + 3 * 0.000070578391 ^ 2 +
        2 * 0.797885 * 0.000191072067 * 0.000121580438 + 2 * 0.000191072067 * 0.000070578391 +
        4 * 0.797885 * 0.000121580438 * 0.000070578391 := by gcongr
    _ ≤ (1.57663E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12786 BstLean.Part154.csC Θ ≤ 0.002610990829 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12786 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12786 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035687532057 * 1.57663E-7 / (0.000250157299 : ℝ) := by gcongr
    _ ≤ 0.002610990829 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12786 BstLean.Part154.csC Θ ≤ 0.002896693262 + 0.000659755173 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12786 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035687532057 : ℝ) * ((2 * Θ * 0.000250157686 +
        (6863 / 10000) * 0.000250157686 * 12786 * 0.001000693323) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002896693262 + 0.000659755173 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12786 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12786 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12786 0.011 Θ ∧ gammaRatio 12786 0.011 Θ ≤ 0.000085997744 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12786 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035687532057 : ℝ) * 0.525 / ((1 - 0.011) * 12786) := by gcongr
      _ ≤ (0.000085997744 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12786 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12786 0.011 Θ) :=
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
    badAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12786 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12786 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12786 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12786 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12786 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12786 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12786 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12786 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12786 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12786 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035687532057 : ℝ) * 12786 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003456897821 + 0.003270746002 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12786

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12786
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12786 BstLean.Part154.csC) (piBar (rhoBar 12786 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12786 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12786 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12786 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12786 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12786 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12786 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12786 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12786 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12786 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052305596723 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12786) ≤ 0.010561446020 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12786 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035687532057)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010561446020 + 2 * 0.737676 / 12786) := by gcongr
    _ ≤ (0.052305596723 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12786 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12786

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12786
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507431307 : ℝ) ≤ plow 12786 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12786) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680639473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370770186) : eMP 12786 0.011 xi bn ≤ 0.001180224762 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12786 : ℝ) * (1 - 0.011))) ≤ 0.000583568431 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370770186 / (12786 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583568431 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583568431 : ℝ) + 3.141593 * 0.052680639473 / (12786 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180224762 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680639473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370770186) : PiBarMP 12786 12 0.011 xi bn ≤ 0.160702463361 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12786 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037023913705 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.451562905990 : ℝ) ≤ √((12786 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.075196219153 : ℝ) ≤ √(12786 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12786) ≤ 0.123213655414 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037023913705 + 0.052680639473 * 1.772454 / (2 * (112.451562905990 : ℝ))) * (1 + 0.001180224762) +
        8 / (12786 * 113.075196219153) + 0.123213655414 := by gcongr
    _ ≤ (0.160702463361 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680639473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370770186) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281828230625) :
    parallelOracle 12786 0.011 xi bn cd ≤ 0.161686359310 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12786 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12786 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507431307 : ℝ) ≤ plow 12786 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.075196219153 : ℝ) ≤ √(12786 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281828230625 : ℝ) / (2 * 0.560507431307 * 113.075196219153)) * 0.160702463361 +
        0.281828230625 ^ 2 / (2 * 0.560507431307 * 113.075196219153) := by gcongr
    _ ≤ (0.161686359310 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680639473) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370770186)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281828230625) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12786 12786 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507431307 : ℝ) ≤ plow 12786 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.075196219153 : ℝ) ≤ √(12786 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12786 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12786 Θ 1.22 ≤ 0.011727598487 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.075196219153 := by gcongr <;> linarith
      _ ≤ (0.011727598487 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12786 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12786 12786 0.011 ≤ 0.008453551587 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12786 12786 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12786 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12786 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12786 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12786 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161686359310 + 0.011727598487 + (0.008453551587 : ℝ) *
        (1 + 2 * (0.281828230625 + 0.011727598487) / (0.560507431307 * 113.075196219153))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12786]

end BstLean.Part269.N12786

/-! The original eight local profiles supply actual 12786 moment certificates. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12786 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052680639473 ∧
    0 ≤ bN 12786 BstLean.Part154.csC (groupTheta g) ∧ bN 12786 BstLean.Part154.csC (groupTheta g) ≤ 0.001370770186 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12786 12786 0.011
      (momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12786 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12786 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12786 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229522633902 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12786 0.011
      (momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12786 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12786
/-! The actual computed-centre upper energy formula at 12786. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12786

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12786)
open BstLean.Part268 (cell12786)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085243350066
  | 2 => 0.086181650154
  | 3 => 0.087117454963
  | 4 => 0.088052035313
  | 5 => 0.088986933023
  | 6 => 0.089924001768
  | 7 => 0.090865451888
  | 8 => 0.091813899214
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12786 12786 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12786 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12786

/-! Actual upper energy certificates on all 43 source endpoints at 12786. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12786)
open BstLean.Part268 (cell12786)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12786 (gMinus 12786) (1 - (cell12786 i).lower) ≤ 1 ∧
    energyUpper 12786 (gMinus 12786) (BstLean.Part211.gPlus 12786)
      (finiteEnergy 12786 12786 0.011) (1 - (cell12786 i).lower) ≤
      (cell12786 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨10,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨11,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨12,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨13,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨14,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨15,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨16,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨17,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨18,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨19,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨20,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨21,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨22,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨23,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨24,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨25,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨26,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨27,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨28,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨29,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨30,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨31,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨32,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨33,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨34,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨35,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨36,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨37,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨38,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨39,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨40,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨41,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨42,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨43,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨44,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨45,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨46,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨47,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨48,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨49,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨50,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨51,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12786) (by norm_num)
        (q := 1 - (cell12786 ⟨52,by decide⟩).lower)
        (by norm_num [cell12786]) (by norm_num [cell12786])
      exact ⟨E.1,E.2.trans (by norm_num [cell12786])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12786

/-! Source-cell containment and simple scalar guards at 12786. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12786)
open BstLean.Part268 (cell12786)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12786 ⟨10,by decide⟩).lower ∧ (cell12786 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12786 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12786 ⟨11,by decide⟩).lower ∧ (cell12786 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12786 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12786 ⟨12,by decide⟩).lower ∧ (cell12786 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12786 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12786 ⟨13,by decide⟩).lower ∧ (cell12786 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12786 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12786 ⟨14,by decide⟩).lower ∧ (cell12786 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12786 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12786 ⟨15,by decide⟩).lower ∧ (cell12786 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12786 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12786 ⟨16,by decide⟩).lower ∧ (cell12786 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12786 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12786 ⟨17,by decide⟩).lower ∧ (cell12786 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12786 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12786 ⟨18,by decide⟩).lower ∧ (cell12786 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12786 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12786 ⟨19,by decide⟩).lower ∧ (cell12786 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12786 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12786 ⟨20,by decide⟩).lower ∧ (cell12786 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12786 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12786 ⟨21,by decide⟩).lower ∧ (cell12786 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12786 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12786 ⟨22,by decide⟩).lower ∧ (cell12786 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12786 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12786 ⟨23,by decide⟩).lower ∧ (cell12786 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12786 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12786 ⟨24,by decide⟩).lower ∧ (cell12786 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12786 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12786 ⟨25,by decide⟩).lower ∧ (cell12786 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12786 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12786 ⟨26,by decide⟩).lower ∧ (cell12786 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12786 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12786 ⟨27,by decide⟩).lower ∧ (cell12786 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12786 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12786 ⟨28,by decide⟩).lower ∧ (cell12786 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12786 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12786 ⟨29,by decide⟩).lower ∧ (cell12786 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12786 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12786 ⟨30,by decide⟩).lower ∧ (cell12786 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12786 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12786 ⟨31,by decide⟩).lower ∧ (cell12786 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12786 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12786 ⟨32,by decide⟩).lower ∧ (cell12786 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12786 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12786 ⟨33,by decide⟩).lower ∧ (cell12786 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12786 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12786 ⟨34,by decide⟩).lower ∧ (cell12786 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12786 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12786 ⟨35,by decide⟩).lower ∧ (cell12786 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12786 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12786 ⟨36,by decide⟩).lower ∧ (cell12786 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12786 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12786 ⟨37,by decide⟩).lower ∧ (cell12786 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12786 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12786 ⟨38,by decide⟩).lower ∧ (cell12786 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12786 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12786 ⟨39,by decide⟩).lower ∧ (cell12786 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12786 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12786 ⟨40,by decide⟩).lower ∧ (cell12786 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12786 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12786 ⟨41,by decide⟩).lower ∧ (cell12786 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12786 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12786 ⟨42,by decide⟩).lower ∧ (cell12786 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12786 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12786 ⟨43,by decide⟩).lower ∧ (cell12786 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12786 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12786 ⟨44,by decide⟩).lower ∧ (cell12786 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12786 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12786 ⟨45,by decide⟩).lower ∧ (cell12786 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12786 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12786 ⟨46,by decide⟩).lower ∧ (cell12786 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12786 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12786 ⟨47,by decide⟩).lower ∧ (cell12786 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12786 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12786 ⟨48,by decide⟩).lower ∧ (cell12786 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12786 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12786 ⟨49,by decide⟩).lower ∧ (cell12786 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12786 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12786 ⟨50,by decide⟩).lower ∧ (cell12786 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12786 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12786 ⟨51,by decide⟩).lower ∧ (cell12786 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12786 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12786 ⟨52,by decide⟩).lower ∧ (cell12786 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12786 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12786 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12786 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12786,cell12786,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12786 i).lower ∧
    (cell12786 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12786 i).upper ≤ (0.532 : ℝ) ∧
    (cell12786 i).centre ≤ (0.1 : ℝ) ∧ (cell12786 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12786 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12786 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12786

/-! The local source numeric instances at 12786 have no network premises. -/
namespace BstLean.Part269.N12786
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12786)
open BstLean.Part268 (cell12786)

noncomputable def sourceNumerics12786 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12786 (cell12786 i)
      scalarRow12786.M scalarRow12786.H scalarRow12786.xi := by
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
    energy_allowance := scalarRow12786.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12786]
    centre_nonneg := (scalarRow12786.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12786])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12786
/-! Actual 12787 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12787 ≤ (1.035686124336 : ℝ) := by
  have hr : (113.079617968933 : ℝ) ≤ √(12787 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.079617968933 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12787 12787 (11 / 1000) ≤
    (0.008453221025 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12787) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.079617968933 : ℝ) ≤ √(12787 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12787)
  have hdiv : K / √(12787 : ℝ) ≤ K / 113.079617968933 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.079617968933 ≤ (0.008453221025 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12787.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12787 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12787 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12787 := gPlus_lower 12787
end BstLean.Part269.N12787

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12787
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035686124335 : ℝ) ≤ wn 12787 := by
  have hn : √(12787 : ℝ) ≤ 113.079617968934 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12787 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.079617968934 ≤ 2 / √(12787 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250137396 : ℝ) ≤ rhoBar 12787 BstLean.Part154.csC ∧
    rhoBar 12787 BstLean.Part154.csC ≤ 0.000250137783 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035686124335 : ℝ) / (1.295212 * 12787) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035686124336 : ℝ) / (1.29521 * 12787) := by gcongr
      _ ≤ (0.000250137783 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12787 BstLean.Part154.csC) ≤ 0.001000613701 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12787 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) ≤ 0.000191056865 ∧
    cc1 (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) ≤ 0.000121570764 ∧
    cc2 (rhoBar 12787 BstLean.Part154.csC) ≤ 0.000070572775 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12787 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12787 BstLean.Part154.csC * nuR (rhoBar 12787 BstLean.Part154.csC)) ≤ 0.000500291209 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250137783 : ℝ) * 0.001000613701 := by gcongr
      _ ≤ (0.000500291209 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12787 BstLean.Part154.csC) * nuR (rhoBar 12787 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001000613701 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12787 BstLean.Part154.csC) * rhoBar 12787 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250137783 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250137783 / 2 + 0.399 * 0.001000613701 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191056865 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500291209 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121570764 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250137783 / 1.414213562 := by gcongr
      _ ≤ (0.000070572775 : ℝ) := by norm_num

end BstLean.Part269.N12787

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12787
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) ≤ 1.57638E-7 := by
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12787 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12787 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191056865 : ℝ) ^ 2 + 0.000121570764 ^ 2 + 3 * 0.000070572775 ^ 2 +
        2 * 0.797885 * 0.000191056865 * 0.000121570764 + 2 * 0.000191056865 * 0.000070572775 +
        4 * 0.797885 * 0.000121570764 * 0.000070572775 := by gcongr
    _ ≤ (1.57638E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12787 BstLean.Part154.csC Θ ≤ 0.002610780985 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12787 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12787 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035686124336 * 1.57638E-7 / (0.000250137396 : ℝ) := by gcongr
    _ ≤ 0.002610780985 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12787 BstLean.Part154.csC Θ ≤ 0.002896454912 + 0.000659701785 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12787 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035686124336 : ℝ) * ((2 * Θ * 0.000250137783 +
        (6863 / 10000) * 0.000250137783 * 12787 * 0.001000613701) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002896454912 + 0.000659701785 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12787 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12787 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12787 0.011 Θ ∧ gammaRatio 12787 0.011 Θ ≤ 0.000085990902 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12787 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035686124336 : ℝ) * 0.525 / ((1 - 0.011) * 12787) := by gcongr
      _ ≤ (0.000085990902 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12787 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12787 0.011 Θ) :=
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
    badAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560204559 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12787 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12787 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12787 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12787 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12787 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12787 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12787 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12787 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12787 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12787 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035686124336 : ℝ) * 12787 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560204559 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003456659471 + 0.003270482770 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12787

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12787
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12787 BstLean.Part154.csC) (piBar (rhoBar 12787 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12787 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12787 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12787 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12787 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12787 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12787 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12787 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12787 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12787 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052303529315 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12787) ≤ 0.010561033036 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12787 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035686124336)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010561033036 + 2 * 0.737676 / 12787) := by gcongr
    _ ≤ (0.052303529315 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12787 12 ≤ 0.0015 := by
  exact BstLean.Part269.S17.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12787

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12787
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560507475920 : ℝ) ≤ plow 12787 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12787) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680262926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370660018) : eMP 12787 0.011 xi bn ≤ 0.001180131105 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12787 : ℝ) * (1 - 0.011))) ≤ 0.000583522161 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001370660018 / (12787 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000583522161 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000583522161 : ℝ) + 3.141593 * 0.052680262926 / (12787 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001180131105 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680262926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370660018) : PiBarMP 12787 12 0.011 xi bn ≤ 0.160696132379 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12787 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037022425880 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.455960268898 : ℝ) ≤ √((12787 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.079617968933 : ℝ) ≤ √(12787 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12787) ≤ 0.123208837393 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037022425880 + 0.052680262926 * 1.772454 / (2 * (112.455960268898 : ℝ))) * (1 + 0.001180131105) +
        8 / (12787 * 113.079617968933) + 0.123208837393 := by gcongr
    _ ≤ (0.160696132379 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680262926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370660018) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281825342932) :
    parallelOracle 12787 0.011 xi bn cd ≤ 0.161679959200 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12787 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12787 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560507475920 : ℝ) ≤ plow 12787 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.079617968933 : ℝ) ≤ √(12787 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281825342932 : ℝ) / (2 * 0.560507475920 * 113.079617968933)) * 0.160696132379 +
        0.281825342932 ^ 2 / (2 * 0.560507475920 * 113.079617968933) := by gcongr
    _ ≤ (0.161679959200 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052680262926) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001370660018)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281825342932) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12787 12787 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560507475920 : ℝ) ≤ plow 12787 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.079617968933 : ℝ) ≤ √(12787 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12787 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12787 Θ 1.22 ≤ 0.011727139903 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.079617968933 := by gcongr <;> linarith
      _ ≤ (0.011727139903 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12787 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12787 12787 0.011 ≤ 0.008453221025 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12787 12787 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12787 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12787 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12787 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12787 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161679959200 + 0.011727139903 + (0.008453221025 : ℝ) *
        (1 + 2 * (0.281825342932 + 0.011727139903) / (0.560507475920 * 113.079617968933))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12787]

end BstLean.Part269.N12787

/-! The original eight local profiles supply actual 12787 moment certificates. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12787 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052680262926 ∧
    0 ≤ bN 12787 BstLean.Part154.csC (groupTheta g) ∧ bN 12787 BstLean.Part154.csC (groupTheta g) ≤ 0.001370660018 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12787 12787 0.011
      (momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12787 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12787 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12787 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229521813617 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12787 0.011
      (momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12787 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12787
/-! The actual computed-centre upper energy formula at 12787. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12787

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12787)
open BstLean.Part268 (cell12787)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085240523574
  | 2 => 0.086178773724
  | 3 => 0.087114521635
  | 4 => 0.088049036501
  | 5 => 0.088983858225
  | 6 => 0.089920838239
  | 7 => 0.090862184271
  | 8 => 0.091810509134
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12787 12787 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12787 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003459522332 + 0.003273654356 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S17.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S17.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12787

/-! Actual upper energy certificates on all 43 source endpoints at 12787. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12787)
open BstLean.Part268 (cell12787)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12787 (gMinus 12787) (1 - (cell12787 i).lower) ≤ 1 ∧
    energyUpper 12787 (gMinus 12787) (BstLean.Part211.gPlus 12787)
      (finiteEnergy 12787 12787 0.011) (1 - (cell12787 i).lower) ≤
      (cell12787 i).energy := by
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
      have E := BstLean.Part269.S17.uniformEnergy10 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨10,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy11 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨11,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy12 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨12,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy13 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨13,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy14 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨14,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy15 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨15,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy16 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨16,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy17 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨17,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy18 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨18,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy19 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨19,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy20 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨20,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy21 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨21,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy22 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨22,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy23 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨23,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy24 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨24,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy25 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨25,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy26 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨26,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy27 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨27,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy28 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨28,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy29 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨29,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy30 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨30,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy31 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨31,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy32 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨32,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy33 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨33,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy34 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨34,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy35 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨35,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy36 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨36,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy37 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨37,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy38 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨38,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy39 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨39,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy40 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨40,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy41 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨41,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy42 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨42,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy43 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨43,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy44 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨44,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy45 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨45,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy46 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨46,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy47 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨47,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy48 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨48,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy49 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨49,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy50 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨50,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy51 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨51,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S17.uniformEnergy52 (n := 12787) (by norm_num)
        (q := 1 - (cell12787 ⟨52,by decide⟩).lower)
        (by norm_num [cell12787]) (by norm_num [cell12787])
      exact ⟨E.1,E.2.trans (by norm_num [cell12787])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12787

/-! Source-cell containment and simple scalar guards at 12787. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12787)
open BstLean.Part268 (cell12787)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12787 ⟨10,by decide⟩).lower ∧ (cell12787 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12787 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12787 ⟨11,by decide⟩).lower ∧ (cell12787 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12787 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12787 ⟨12,by decide⟩).lower ∧ (cell12787 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12787 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12787 ⟨13,by decide⟩).lower ∧ (cell12787 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12787 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12787 ⟨14,by decide⟩).lower ∧ (cell12787 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12787 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12787 ⟨15,by decide⟩).lower ∧ (cell12787 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12787 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12787 ⟨16,by decide⟩).lower ∧ (cell12787 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12787 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12787 ⟨17,by decide⟩).lower ∧ (cell12787 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12787 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12787 ⟨18,by decide⟩).lower ∧ (cell12787 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12787 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12787 ⟨19,by decide⟩).lower ∧ (cell12787 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12787 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12787 ⟨20,by decide⟩).lower ∧ (cell12787 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12787 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12787 ⟨21,by decide⟩).lower ∧ (cell12787 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12787 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12787 ⟨22,by decide⟩).lower ∧ (cell12787 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12787 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12787 ⟨23,by decide⟩).lower ∧ (cell12787 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12787 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12787 ⟨24,by decide⟩).lower ∧ (cell12787 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12787 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12787 ⟨25,by decide⟩).lower ∧ (cell12787 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12787 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12787 ⟨26,by decide⟩).lower ∧ (cell12787 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12787 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12787 ⟨27,by decide⟩).lower ∧ (cell12787 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12787 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12787 ⟨28,by decide⟩).lower ∧ (cell12787 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12787 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12787 ⟨29,by decide⟩).lower ∧ (cell12787 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12787 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12787 ⟨30,by decide⟩).lower ∧ (cell12787 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12787 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12787 ⟨31,by decide⟩).lower ∧ (cell12787 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12787 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12787 ⟨32,by decide⟩).lower ∧ (cell12787 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12787 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12787 ⟨33,by decide⟩).lower ∧ (cell12787 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12787 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12787 ⟨34,by decide⟩).lower ∧ (cell12787 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12787 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12787 ⟨35,by decide⟩).lower ∧ (cell12787 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12787 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12787 ⟨36,by decide⟩).lower ∧ (cell12787 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12787 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12787 ⟨37,by decide⟩).lower ∧ (cell12787 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12787 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12787 ⟨38,by decide⟩).lower ∧ (cell12787 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12787 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12787 ⟨39,by decide⟩).lower ∧ (cell12787 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12787 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12787 ⟨40,by decide⟩).lower ∧ (cell12787 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12787 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12787 ⟨41,by decide⟩).lower ∧ (cell12787 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12787 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12787 ⟨42,by decide⟩).lower ∧ (cell12787 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12787 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12787 ⟨43,by decide⟩).lower ∧ (cell12787 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12787 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12787 ⟨44,by decide⟩).lower ∧ (cell12787 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12787 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12787 ⟨45,by decide⟩).lower ∧ (cell12787 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12787 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12787 ⟨46,by decide⟩).lower ∧ (cell12787 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12787 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12787 ⟨47,by decide⟩).lower ∧ (cell12787 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12787 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12787 ⟨48,by decide⟩).lower ∧ (cell12787 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12787 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12787 ⟨49,by decide⟩).lower ∧ (cell12787 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12787 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12787 ⟨50,by decide⟩).lower ∧ (cell12787 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12787 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12787 ⟨51,by decide⟩).lower ∧ (cell12787 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12787 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12787 ⟨52,by decide⟩).lower ∧ (cell12787 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12787 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12787 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12787 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12787,cell12787,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12787 i).lower ∧
    (cell12787 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12787 i).upper ≤ (0.532 : ℝ) ∧
    (cell12787 i).centre ≤ (0.1 : ℝ) ∧ (cell12787 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12787 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12787 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12787

/-! The local source numeric instances at 12787 have no network premises. -/
namespace BstLean.Part269.N12787
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12787)
open BstLean.Part268 (cell12787)

noncomputable def sourceNumerics12787 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12787 (cell12787 i)
      scalarRow12787.M scalarRow12787.H scalarRow12787.xi := by
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
    energy_allowance := scalarRow12787.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12787]
    centre_nonneg := (scalarRow12787.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D17.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12787])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12787