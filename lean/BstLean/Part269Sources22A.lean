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
import BstLean.Part269Direction22
import BstLean.Part269Shared22
import BstLean.Part269Finite
import BstLean.Part269Rows22
import BstLean.Part269Source
/-! Actual 12900 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12900 ≤ (1.035528113773 : ℝ) := by
  have hr : (113.578166916005 : ℝ) ≤ √(12900 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.578166916005 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12900 12900 (11 / 1000) ≤
    (0.008416115510 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12900) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.578166916005 : ℝ) ≤ √(12900 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12900)
  have hdiv : K / √(12900 : ℝ) ≤ K / 113.578166916005 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.578166916005 ≤ (0.008416115510 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12900.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12900 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12900 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12900 := gPlus_lower 12900
end BstLean.Part269.N12900

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12900
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035528113772 : ℝ) ≤ wn 12900 := by
  have hn : √(12900 : ℝ) ≤ 113.578166916006 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12900 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.578166916006 ≤ 2 / √(12900 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247908441 : ℝ) ≤ rhoBar 12900 BstLean.Part154.csC ∧
    rhoBar 12900 BstLean.Part154.csC ≤ 0.000247908825 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035528113772 : ℝ) / (1.295212 * 12900) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035528113773 : ℝ) / (1.29521 * 12900) := by gcongr
      _ ≤ (0.000247908825 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12900 BstLean.Part154.csC) ≤ 0.000991696759 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12900 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) ≤ 0.000189354294 ∧
    cc1 (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) ≤ 0.000120487423 ∧
    cc2 (rhoBar 12900 BstLean.Part154.csC) ≤ 0.000069943907 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12900 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12900 BstLean.Part154.csC * nuR (rhoBar 12900 BstLean.Part154.csC)) ≤ 0.000495833015 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247908825 : ℝ) * 0.000991696759 := by gcongr
      _ ≤ (0.000495833015 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12900 BstLean.Part154.csC) * nuR (rhoBar 12900 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991696759 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12900 BstLean.Part154.csC) * rhoBar 12900 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247908825 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247908825 / 2 + 0.399 * 0.000991696759 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189354294 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495833015 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120487423 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247908825 / 1.414213562 := by gcongr
      _ ≤ (0.000069943907 : ℝ) := by norm_num

end BstLean.Part269.N12900

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12900
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) ≤ 1.54841E-7 := by
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12900 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12900 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189354294 : ℝ) ^ 2 + 0.000120487423 ^ 2 + 3 * 0.000069943907 ^ 2 +
        2 * 0.797885 * 0.000189354294 * 0.000120487423 + 2 * 0.000189354294 * 0.000069943907 +
        4 * 0.797885 * 0.000120487423 * 0.000069943907 := by gcongr
    _ ≤ (1.54841E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12900 BstLean.Part154.csC Θ ≤ 0.002587119794 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12900 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12900 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035528113773 * 1.54841E-7 / (0.000247908441 : ℝ) := by gcongr
    _ ≤ 0.002587119794 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12900 BstLean.Part154.csC Θ ≤ 0.002869767370 + 0.000653723483 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12900 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035528113773 : ℝ) * ((2 * Θ * 0.000247908825 +
        (6863 / 10000) * 0.000247908825 * 12900 * 0.000991696759) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002869767370 + 0.000653723483 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12900 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12900 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12900 0.011 Θ ∧ gammaRatio 12900 0.011 Θ ≤ 0.000085224644 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12900 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035528113773 : ℝ) * 0.525 / ((1 - 0.011) * 12900) := by gcongr
      _ ≤ (0.000085224644 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12900 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12900 0.011 Θ) :=
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
    badAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12900 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12900 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12900 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12900 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12900 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12900 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12900 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12900 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12900 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12900 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035528113773 : ℝ) * 12900 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333438387 + 0.003240843277 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12900

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12900
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12900 BstLean.Part154.csC) (piBar (rhoBar 12900 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12900 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12900 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12900 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12900 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12900 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12900 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12900 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12900 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12900 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052071473873 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12900) ≤ 0.010514675607 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12900 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035528113773)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010514675607 + 2 * 0.737676 / 12900) := by gcongr
    _ ≤ (0.052071473873 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12900 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12900

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12900
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512472658 : ℝ) ≤ plow 12900 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12900) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541481108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358237892) : eMP 12900 0.011 xi bn ≤ 0.001169582419 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12900 : ℝ) * (1 - 0.011))) ≤ 0.000578322223 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358237892 / (12900 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578322223 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578322223 : ℝ) + 3.141593 * 0.052541481108 / (12900 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169582419 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541481108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358237892) : PiBarMP 12900 12 0.011 xi bn ≤ 0.159983584356 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12900 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036854279155 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.951759614447 : ℝ) ≤ √((12900 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.578166916005 : ℝ) ≤ √(12900 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12900) ≤ 0.122668014823 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036854279155 + 0.052541481108 * 1.772454 / (2 * (112.951759614447 : ℝ))) * (1 + 0.001169582419) +
        8 / (12900 * 113.578166916005) + 0.122668014823 := by gcongr
    _ ≤ (0.159983584356 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541481108)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358237892) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281290759947) :
    parallelOracle 12900 0.011 xi bn cd ≤ 0.160958470759 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12900 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12900 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512472658 : ℝ) ≤ plow 12900 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.578166916005 : ℝ) ≤ √(12900 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281290759947 : ℝ) / (2 * 0.560512472658 * 113.578166916005)) * 0.159983584356 +
        0.281290759947 ^ 2 / (2 * 0.560512472658 * 113.578166916005) := by gcongr
    _ ≤ (0.160958470759 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541481108) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358237892)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281290759947) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12900 12900 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512472658 : ℝ) ≤ plow 12900 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.578166916005 : ℝ) ≤ √(12900 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12900 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12900 Θ 1.22 ≤ 0.011675663872 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.578166916005 := by gcongr <;> linarith
      _ ≤ (0.011675663872 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12900 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12900 12900 0.011 ≤ 0.008416115510 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12900 12900 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12900 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12900 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12900 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12900 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160958470759 + 0.011675663872 + (0.008416115510 : ℝ) *
        (1 + 2 * (0.281290759947 + 0.011675663872) / (0.560512472658 * 113.578166916005))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12900]

end BstLean.Part269.N12900

/-! The original eight local profiles supply actual 12900 moment certificates. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12900 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052541481108 ∧
    0 ≤ bN 12900 BstLean.Part154.csC (groupTheta g) ∧ bN 12900 BstLean.Part154.csC (groupTheta g) ≤ 0.001358237892 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12900 12900 0.011
      (momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12900 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12900 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12900 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229219286074 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12900 0.011
      (momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12900 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12900
/-! The actual computed-centre upper energy formula at 12900. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12900

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12900)
open BstLean.Part268 (cell12900)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084927301863
  | 2 => 0.085860153207
  | 3 => 0.086789773267
  | 4 => 0.087717259430
  | 5 => 0.088643948800
  | 6 => 0.089571455041
  | 7 => 0.090501708907
  | 8 => 0.091437002558
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12900 12900 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12900 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12900

/-! Actual upper energy certificates on all 43 source endpoints at 12900. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12900)
open BstLean.Part268 (cell12900)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12900 (gMinus 12900) (1 - (cell12900 i).lower) ≤ 1 ∧
    energyUpper 12900 (gMinus 12900) (BstLean.Part211.gPlus 12900)
      (finiteEnergy 12900 12900 0.011) (1 - (cell12900 i).lower) ≤
      (cell12900 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨10,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨11,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨12,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨13,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨14,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨15,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨16,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨17,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨18,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨19,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨20,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨21,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨22,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨23,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨24,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨25,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨26,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨27,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨28,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨29,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨30,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨31,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨32,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨33,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨34,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨35,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨36,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨37,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨38,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨39,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨40,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨41,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨42,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨43,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨44,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨45,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨46,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨47,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨48,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨49,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨50,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨51,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12900) (by norm_num)
        (q := 1 - (cell12900 ⟨52,by decide⟩).lower)
        (by norm_num [cell12900]) (by norm_num [cell12900])
      exact ⟨E.1,E.2.trans (by norm_num [cell12900])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12900

/-! Source-cell containment and simple scalar guards at 12900. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12900)
open BstLean.Part268 (cell12900)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12900 ⟨10,by decide⟩).lower ∧ (cell12900 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12900 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12900 ⟨11,by decide⟩).lower ∧ (cell12900 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12900 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12900 ⟨12,by decide⟩).lower ∧ (cell12900 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12900 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12900 ⟨13,by decide⟩).lower ∧ (cell12900 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12900 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12900 ⟨14,by decide⟩).lower ∧ (cell12900 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12900 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12900 ⟨15,by decide⟩).lower ∧ (cell12900 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12900 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12900 ⟨16,by decide⟩).lower ∧ (cell12900 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12900 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12900 ⟨17,by decide⟩).lower ∧ (cell12900 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12900 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12900 ⟨18,by decide⟩).lower ∧ (cell12900 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12900 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12900 ⟨19,by decide⟩).lower ∧ (cell12900 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12900 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12900 ⟨20,by decide⟩).lower ∧ (cell12900 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12900 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12900 ⟨21,by decide⟩).lower ∧ (cell12900 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12900 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12900 ⟨22,by decide⟩).lower ∧ (cell12900 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12900 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12900 ⟨23,by decide⟩).lower ∧ (cell12900 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12900 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12900 ⟨24,by decide⟩).lower ∧ (cell12900 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12900 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12900 ⟨25,by decide⟩).lower ∧ (cell12900 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12900 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12900 ⟨26,by decide⟩).lower ∧ (cell12900 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12900 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12900 ⟨27,by decide⟩).lower ∧ (cell12900 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12900 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12900 ⟨28,by decide⟩).lower ∧ (cell12900 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12900 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12900 ⟨29,by decide⟩).lower ∧ (cell12900 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12900 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12900 ⟨30,by decide⟩).lower ∧ (cell12900 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12900 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12900 ⟨31,by decide⟩).lower ∧ (cell12900 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12900 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12900 ⟨32,by decide⟩).lower ∧ (cell12900 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12900 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12900 ⟨33,by decide⟩).lower ∧ (cell12900 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12900 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12900 ⟨34,by decide⟩).lower ∧ (cell12900 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12900 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12900 ⟨35,by decide⟩).lower ∧ (cell12900 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12900 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12900 ⟨36,by decide⟩).lower ∧ (cell12900 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12900 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12900 ⟨37,by decide⟩).lower ∧ (cell12900 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12900 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12900 ⟨38,by decide⟩).lower ∧ (cell12900 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12900 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12900 ⟨39,by decide⟩).lower ∧ (cell12900 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12900 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12900 ⟨40,by decide⟩).lower ∧ (cell12900 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12900 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12900 ⟨41,by decide⟩).lower ∧ (cell12900 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12900 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12900 ⟨42,by decide⟩).lower ∧ (cell12900 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12900 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12900 ⟨43,by decide⟩).lower ∧ (cell12900 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12900 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12900 ⟨44,by decide⟩).lower ∧ (cell12900 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12900 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12900 ⟨45,by decide⟩).lower ∧ (cell12900 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12900 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12900 ⟨46,by decide⟩).lower ∧ (cell12900 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12900 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12900 ⟨47,by decide⟩).lower ∧ (cell12900 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12900 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12900 ⟨48,by decide⟩).lower ∧ (cell12900 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12900 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12900 ⟨49,by decide⟩).lower ∧ (cell12900 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12900 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12900 ⟨50,by decide⟩).lower ∧ (cell12900 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12900 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12900 ⟨51,by decide⟩).lower ∧ (cell12900 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12900 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12900 ⟨52,by decide⟩).lower ∧ (cell12900 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12900 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12900 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12900 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12900,cell12900,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12900 i).lower ∧
    (cell12900 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12900 i).upper ≤ (0.532 : ℝ) ∧
    (cell12900 i).centre ≤ (0.1 : ℝ) ∧ (cell12900 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12900 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12900 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12900

/-! The local source numeric instances at 12900 have no network premises. -/
namespace BstLean.Part269.N12900
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12900)
open BstLean.Part268 (cell12900)

noncomputable def sourceNumerics12900 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12900 (cell12900 i)
      scalarRow12900.M scalarRow12900.H scalarRow12900.xi := by
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
    energy_allowance := scalarRow12900.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12900]
    centre_nonneg := (scalarRow12900.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12900])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12900
/-! Actual 12901 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12901 ≤ (1.035526724777 : ℝ) := by
  have hr : (113.582569085225 : ℝ) ≤ √(12901 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.582569085225 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12901 12901 (11 / 1000) ≤
    (0.008415789320 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12901) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.582569085225 : ℝ) ≤ √(12901 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12901)
  have hdiv : K / √(12901 : ℝ) ≤ K / 113.582569085225 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.582569085225 ≤ (0.008415789320 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12901.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12901 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12901 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12901 := gPlus_lower 12901
end BstLean.Part269.N12901

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12901
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035526724776 : ℝ) ≤ wn 12901 := by
  have hn : √(12901 : ℝ) ≤ 113.582569085226 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12901 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.582569085226 ≤ 2 / √(12901 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247888893 : ℝ) ≤ rhoBar 12901 BstLean.Part154.csC ∧
    rhoBar 12901 BstLean.Part154.csC ≤ 0.000247889276 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035526724776 : ℝ) / (1.295212 * 12901) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035526724777 : ℝ) / (1.29521 * 12901) := by gcongr
      _ ≤ (0.000247889276 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12901 BstLean.Part154.csC) ≤ 0.000991618554 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12901 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) ≤ 0.000189339362 ∧
    cc1 (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) ≤ 0.000120477922 ∧
    cc2 (rhoBar 12901 BstLean.Part154.csC) ≤ 0.000069938392 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12901 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12901 BstLean.Part154.csC * nuR (rhoBar 12901 BstLean.Part154.csC)) ≤ 0.000495793915 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247889276 : ℝ) * 0.000991618554 := by gcongr
      _ ≤ (0.000495793915 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12901 BstLean.Part154.csC) * nuR (rhoBar 12901 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991618554 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12901 BstLean.Part154.csC) * rhoBar 12901 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247889276 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247889276 / 2 + 0.399 * 0.000991618554 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189339362 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495793915 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120477922 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247889276 / 1.414213562 := by gcongr
      _ ≤ (0.000069938392 : ℝ) := by norm_num

end BstLean.Part269.N12901

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12901
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) ≤ 1.54817E-7 := by
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12901 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12901 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189339362 : ℝ) ^ 2 + 0.000120477922 ^ 2 + 3 * 0.000069938392 ^ 2 +
        2 * 0.797885 * 0.000189339362 * 0.000120477922 + 2 * 0.000189339362 * 0.000069938392 +
        4 * 0.797885 * 0.000120477922 * 0.000069938392 := by gcongr
    _ ≤ (1.54817E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12901 BstLean.Part154.csC Θ ≤ 0.002586919310 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12901 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12901 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035526724777 * 1.54817E-7 / (0.000247888893 : ℝ) := by gcongr
    _ ≤ 0.002586919310 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12901 BstLean.Part154.csC Θ ≤ 0.002869533360 + 0.000653671057 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12901 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035526724777 : ℝ) * ((2 * Θ * 0.000247889276 +
        (6863 / 10000) * 0.000247889276 * 12901 * 0.000991618554) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002869533360 + 0.000653671057 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12901 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12901 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12901 0.011 Θ ∧ gammaRatio 12901 0.011 Θ ≤ 0.000085217923 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12901 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035526724777 : ℝ) * 0.525 / ((1 - 0.011) * 12901) := by gcongr
      _ ≤ (0.000085217923 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12901 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12901 0.011 Θ) :=
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
    badAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12901 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12901 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12901 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12901 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12901 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12901 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12901 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12901 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12901 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12901 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035526724777 : ℝ) * 12901 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333204377 + 0.003240590367 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12901

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12901
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12901 BstLean.Part154.csC) (piBar (rhoBar 12901 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12901 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12901 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12901 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12901 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12901 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12901 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12901 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12901 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12901 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052069434001 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12901) ≤ 0.010514268085 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12901 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035526724777)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010514268085 + 2 * 0.737676 / 12901) := by gcongr
    _ ≤ (0.052069434001 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12901 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12901

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12901
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512516487 : ℝ) ≤ plow 12901 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12901) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541114320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358132638) : eMP 12901 0.011 xi bn ≤ 0.001169491682 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12901 : ℝ) * (1 - 0.011))) ≤ 0.000578277401 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358132638 / (12901 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578277401 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578277401 : ℝ) + 3.141593 * 0.052541114320 / (12901 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169491682 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541114320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358132638) : PiBarMP 12901 12 0.011 xi bn ≤ 0.159977377492 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12901 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036852851152 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.956137504785 : ℝ) ≤ √((12901 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.582569085225 : ℝ) ≤ √(12901 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12901) ≤ 0.122663260525 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036852851152 + 0.052541114320 * 1.772454 / (2 * (112.956137504785 : ℝ))) * (1 + 0.001169491682) +
        8 / (12901 * 113.582569085225) + 0.122663260525 := by gcongr
    _ ≤ (0.159977377492 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541114320)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358132638) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281287919992) :
    parallelOracle 12901 0.011 xi bn cd ≤ 0.160952196206 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12901 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12901 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512516487 : ℝ) ≤ plow 12901 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.582569085225 : ℝ) ≤ √(12901 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281287919992 : ℝ) / (2 * 0.560512516487 * 113.582569085225)) * 0.159977377492 +
        0.281287919992 ^ 2 / (2 * 0.560512516487 * 113.582569085225) := by gcongr
    _ ≤ (0.160952196206 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541114320) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358132638)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281287919992) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12901 12901 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512516487 : ℝ) ≤ plow 12901 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.582569085225 : ℝ) ≤ √(12901 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12901 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12901 Θ 1.22 ≤ 0.011675211353 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.582569085225 := by gcongr <;> linarith
      _ ≤ (0.011675211353 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12901 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12901 12901 0.011 ≤ 0.008415789320 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12901 12901 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12901 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12901 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12901 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12901 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160952196206 + 0.011675211353 + (0.008415789320 : ℝ) *
        (1 + 2 * (0.281287919992 + 0.011675211353) / (0.560512516487 * 113.582569085225))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12901]

end BstLean.Part269.N12901

/-! The original eight local profiles supply actual 12901 moment certificates. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12901 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052541114320 ∧
    0 ≤ bN 12901 BstLean.Part154.csC (groupTheta g) ∧ bN 12901 BstLean.Part154.csC (groupTheta g) ≤ 0.001358132638 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12901 12901 0.011
      (momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12901 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12901 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12901 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229218485991 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12901 0.011
      (momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12901 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12901
/-! The actual computed-centre upper energy formula at 12901. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12901

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12901)
open BstLean.Part268 (cell12901)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084924582612
  | 2 => 0.085857388236
  | 3 => 0.086786956609
  | 4 => 0.087714383696
  | 5 => 0.088641004925
  | 6 => 0.089568431988
  | 7 => 0.090498593343
  | 8 => 0.091433778484
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12901 12901 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12901 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12901

/-! Actual upper energy certificates on all 43 source endpoints at 12901. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12901)
open BstLean.Part268 (cell12901)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12901 (gMinus 12901) (1 - (cell12901 i).lower) ≤ 1 ∧
    energyUpper 12901 (gMinus 12901) (BstLean.Part211.gPlus 12901)
      (finiteEnergy 12901 12901 0.011) (1 - (cell12901 i).lower) ≤
      (cell12901 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨10,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨11,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨12,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨13,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨14,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨15,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨16,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨17,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨18,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨19,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨20,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨21,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨22,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨23,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨24,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨25,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨26,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨27,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨28,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨29,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨30,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨31,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨32,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨33,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨34,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨35,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨36,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨37,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨38,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨39,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨40,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨41,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨42,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨43,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨44,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨45,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨46,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨47,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨48,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨49,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨50,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨51,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12901) (by norm_num)
        (q := 1 - (cell12901 ⟨52,by decide⟩).lower)
        (by norm_num [cell12901]) (by norm_num [cell12901])
      exact ⟨E.1,E.2.trans (by norm_num [cell12901])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12901

/-! Source-cell containment and simple scalar guards at 12901. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12901)
open BstLean.Part268 (cell12901)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12901 ⟨10,by decide⟩).lower ∧ (cell12901 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12901 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12901 ⟨11,by decide⟩).lower ∧ (cell12901 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12901 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12901 ⟨12,by decide⟩).lower ∧ (cell12901 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12901 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12901 ⟨13,by decide⟩).lower ∧ (cell12901 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12901 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12901 ⟨14,by decide⟩).lower ∧ (cell12901 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12901 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12901 ⟨15,by decide⟩).lower ∧ (cell12901 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12901 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12901 ⟨16,by decide⟩).lower ∧ (cell12901 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12901 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12901 ⟨17,by decide⟩).lower ∧ (cell12901 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12901 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12901 ⟨18,by decide⟩).lower ∧ (cell12901 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12901 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12901 ⟨19,by decide⟩).lower ∧ (cell12901 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12901 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12901 ⟨20,by decide⟩).lower ∧ (cell12901 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12901 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12901 ⟨21,by decide⟩).lower ∧ (cell12901 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12901 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12901 ⟨22,by decide⟩).lower ∧ (cell12901 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12901 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12901 ⟨23,by decide⟩).lower ∧ (cell12901 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12901 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12901 ⟨24,by decide⟩).lower ∧ (cell12901 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12901 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12901 ⟨25,by decide⟩).lower ∧ (cell12901 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12901 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12901 ⟨26,by decide⟩).lower ∧ (cell12901 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12901 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12901 ⟨27,by decide⟩).lower ∧ (cell12901 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12901 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12901 ⟨28,by decide⟩).lower ∧ (cell12901 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12901 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12901 ⟨29,by decide⟩).lower ∧ (cell12901 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12901 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12901 ⟨30,by decide⟩).lower ∧ (cell12901 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12901 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12901 ⟨31,by decide⟩).lower ∧ (cell12901 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12901 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12901 ⟨32,by decide⟩).lower ∧ (cell12901 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12901 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12901 ⟨33,by decide⟩).lower ∧ (cell12901 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12901 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12901 ⟨34,by decide⟩).lower ∧ (cell12901 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12901 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12901 ⟨35,by decide⟩).lower ∧ (cell12901 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12901 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12901 ⟨36,by decide⟩).lower ∧ (cell12901 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12901 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12901 ⟨37,by decide⟩).lower ∧ (cell12901 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12901 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12901 ⟨38,by decide⟩).lower ∧ (cell12901 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12901 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12901 ⟨39,by decide⟩).lower ∧ (cell12901 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12901 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12901 ⟨40,by decide⟩).lower ∧ (cell12901 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12901 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12901 ⟨41,by decide⟩).lower ∧ (cell12901 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12901 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12901 ⟨42,by decide⟩).lower ∧ (cell12901 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12901 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12901 ⟨43,by decide⟩).lower ∧ (cell12901 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12901 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12901 ⟨44,by decide⟩).lower ∧ (cell12901 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12901 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12901 ⟨45,by decide⟩).lower ∧ (cell12901 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12901 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12901 ⟨46,by decide⟩).lower ∧ (cell12901 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12901 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12901 ⟨47,by decide⟩).lower ∧ (cell12901 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12901 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12901 ⟨48,by decide⟩).lower ∧ (cell12901 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12901 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12901 ⟨49,by decide⟩).lower ∧ (cell12901 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12901 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12901 ⟨50,by decide⟩).lower ∧ (cell12901 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12901 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12901 ⟨51,by decide⟩).lower ∧ (cell12901 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12901 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12901 ⟨52,by decide⟩).lower ∧ (cell12901 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12901 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12901 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12901 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12901,cell12901,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12901 i).lower ∧
    (cell12901 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12901 i).upper ≤ (0.532 : ℝ) ∧
    (cell12901 i).centre ≤ (0.1 : ℝ) ∧ (cell12901 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12901 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12901 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12901

/-! The local source numeric instances at 12901 have no network premises. -/
namespace BstLean.Part269.N12901
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12901)
open BstLean.Part268 (cell12901)

noncomputable def sourceNumerics12901 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12901 (cell12901 i)
      scalarRow12901.M scalarRow12901.H scalarRow12901.xi := by
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
    energy_allowance := scalarRow12901.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12901]
    centre_nonneg := (scalarRow12901.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12901])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12901
/-! Actual 12902 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12902 ≤ (1.035525335943 : ℝ) := by
  have hr : (113.586971083835 : ℝ) ≤ √(12902 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.586971083835 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12902 12902 (11 / 1000) ≤
    (0.008415463169 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12902) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.586971083835 : ℝ) ≤ √(12902 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12902)
  have hdiv : K / √(12902 : ℝ) ≤ K / 113.586971083835 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.586971083835 ≤ (0.008415463169 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12902.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12902 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12902 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12902 := gPlus_lower 12902
end BstLean.Part269.N12902

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12902
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035525335942 : ℝ) ≤ wn 12902 := by
  have hn : √(12902 : ℝ) ≤ 113.586971083836 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12902 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.586971083836 ≤ 2 / √(12902 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247869347 : ℝ) ≤ rhoBar 12902 BstLean.Part154.csC ∧
    rhoBar 12902 BstLean.Part154.csC ≤ 0.000247869731 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035525335942 : ℝ) / (1.295212 * 12902) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035525335943 : ℝ) / (1.29521 * 12902) := by gcongr
      _ ≤ (0.000247869731 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12902 BstLean.Part154.csC) ≤ 0.000991540364 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12902 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) ≤ 0.000189324432 ∧
    cc1 (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) ≤ 0.000120468422 ∧
    cc2 (rhoBar 12902 BstLean.Part154.csC) ≤ 0.000069932877 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12902 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12902 BstLean.Part154.csC * nuR (rhoBar 12902 BstLean.Part154.csC)) ≤ 0.000495754822 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247869731 : ℝ) * 0.000991540364 := by gcongr
      _ ≤ (0.000495754822 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12902 BstLean.Part154.csC) * nuR (rhoBar 12902 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991540364 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12902 BstLean.Part154.csC) * rhoBar 12902 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247869731 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247869731 / 2 + 0.399 * 0.000991540364 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189324432 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495754822 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120468422 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247869731 / 1.414213562 := by gcongr
      _ ≤ (0.000069932877 : ℝ) := by norm_num

end BstLean.Part269.N12902

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12902
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) ≤ 1.54792E-7 := by
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12902 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12902 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189324432 : ℝ) ^ 2 + 0.000120468422 ^ 2 + 3 * 0.000069932877 ^ 2 +
        2 * 0.797885 * 0.000189324432 * 0.000120468422 + 2 * 0.000189324432 * 0.000069932877 +
        4 * 0.797885 * 0.000120468422 * 0.000069932877 := by gcongr
    _ ≤ (1.54792E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12902 BstLean.Part154.csC Θ ≤ 0.002586702063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12902 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12902 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035525335943 * 1.54792E-7 / (0.000247869347 : ℝ) := by gcongr
    _ ≤ 0.002586702063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12902 BstLean.Part154.csC Θ ≤ 0.002869299406 + 0.000653618641 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12902 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035525335943 : ℝ) * ((2 * Θ * 0.000247869731 +
        (6863 / 10000) * 0.000247869731 * 12902 * 0.000991540364) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002869299406 + 0.000653618641 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12902 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12902 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12902 0.011 Θ ∧ gammaRatio 12902 0.011 Θ ≤ 0.000085211204 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12902 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035525335943 : ℝ) * 0.525 / ((1 - 0.011) * 12902) := by gcongr
      _ ≤ (0.000085211204 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12902 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12902 0.011 Θ) :=
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
    badAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12902 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12902 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12902 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12902 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12902 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12902 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12902 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12902 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12902 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12902 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035525335943 : ℝ) * 12902 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003332970423 + 0.003240320704 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12902

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12902
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12902 BstLean.Part154.csC) (piBar (rhoBar 12902 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12902 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12902 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12902 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12902 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12902 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12902 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12902 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12902 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12902 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052067394366 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12902) ≤ 0.010513860610 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12902 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035525335943)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010513860610 + 2 * 0.737676 / 12902) := by gcongr
    _ ≤ (0.052067394366 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12902 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12902

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12902
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512560308 : ℝ) ≤ plow 12902 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12902) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540738793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358018584) : eMP 12902 0.011 xi bn ≤ 0.001169397203 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12902 : ℝ) * (1 - 0.011))) ≤ 0.000578230709 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358018584 / (12902 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578230709 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578230709 : ℝ) + 3.141593 * 0.052540738793 / (12902 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169397203 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540738793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358018584) : PiBarMP 12902 12 0.011 xi bn ≤ 0.159971051381 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12902 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036851303695 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.960515225453 : ℝ) ≤ √((12902 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.586971083835 : ℝ) ≤ √(12902 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12902) ≤ 0.122658506780 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036851303695 + 0.052540738793 * 1.772454 / (2 * (112.960515225453 : ℝ))) * (1 + 0.001169397203) +
        8 / (12902 * 113.586971083835) + 0.122658506780 := by gcongr
    _ ≤ (0.159971051381 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540738793)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358018584) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281285061210) :
    parallelOracle 12902 0.011 xi bn cd ≤ 0.160945802044 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12902 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12902 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512560308 : ℝ) ≤ plow 12902 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.586971083835 : ℝ) ≤ √(12902 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281285061210 : ℝ) / (2 * 0.560512560308 * 113.586971083835)) * 0.159971051381 +
        0.281285061210 ^ 2 / (2 * 0.560512560308 * 113.586971083835) := by gcongr
    _ ≤ (0.160945802044 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540738793) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358018584)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281285061210) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12902 12902 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512560308 : ℝ) ≤ plow 12902 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.586971083835 : ℝ) ≤ √(12902 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12902 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12902 Θ 1.22 ≤ 0.011674758887 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.586971083835 := by gcongr <;> linarith
      _ ≤ (0.011674758887 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12902 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12902 12902 0.011 ≤ 0.008415463169 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12902 12902 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12902 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12902 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12902 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12902 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160945802044 + 0.011674758887 + (0.008415463169 : ℝ) *
        (1 + 2 * (0.281285061210 + 0.011674758887) / (0.560512560308 * 113.586971083835))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12902]

end BstLean.Part269.N12902

/-! The original eight local profiles supply actual 12902 moment certificates. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12902 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052540738793 ∧
    0 ≤ bN 12902 BstLean.Part154.csC (groupTheta g) ∧ bN 12902 BstLean.Part154.csC (groupTheta g) ≤ 0.001358018584 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12902 12902 0.011
      (momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12902 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12902 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12902 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229217666844 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12902 0.011
      (momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12902 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12902
/-! The actual computed-centre upper energy formula at 12902. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12902

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12902)
open BstLean.Part268 (cell12902)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084921864251
  | 2 => 0.085854624189
  | 3 => 0.086784140917
  | 4 => 0.087711508980
  | 5 => 0.088638062131
  | 6 => 0.089565410095
  | 7 => 0.090495479033
  | 8 => 0.091430555779
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12902 12902 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12902 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12902

/-! Actual upper energy certificates on all 43 source endpoints at 12902. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12902)
open BstLean.Part268 (cell12902)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12902 (gMinus 12902) (1 - (cell12902 i).lower) ≤ 1 ∧
    energyUpper 12902 (gMinus 12902) (BstLean.Part211.gPlus 12902)
      (finiteEnergy 12902 12902 0.011) (1 - (cell12902 i).lower) ≤
      (cell12902 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨10,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨11,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨12,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨13,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨14,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨15,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨16,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨17,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨18,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨19,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨20,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨21,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨22,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨23,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨24,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨25,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨26,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨27,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨28,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨29,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨30,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨31,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨32,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨33,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨34,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨35,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨36,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨37,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨38,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨39,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨40,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨41,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨42,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨43,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨44,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨45,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨46,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨47,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨48,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨49,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨50,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨51,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12902) (by norm_num)
        (q := 1 - (cell12902 ⟨52,by decide⟩).lower)
        (by norm_num [cell12902]) (by norm_num [cell12902])
      exact ⟨E.1,E.2.trans (by norm_num [cell12902])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12902

/-! Source-cell containment and simple scalar guards at 12902. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12902)
open BstLean.Part268 (cell12902)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12902 ⟨10,by decide⟩).lower ∧ (cell12902 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12902 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12902 ⟨11,by decide⟩).lower ∧ (cell12902 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12902 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12902 ⟨12,by decide⟩).lower ∧ (cell12902 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12902 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12902 ⟨13,by decide⟩).lower ∧ (cell12902 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12902 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12902 ⟨14,by decide⟩).lower ∧ (cell12902 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12902 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12902 ⟨15,by decide⟩).lower ∧ (cell12902 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12902 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12902 ⟨16,by decide⟩).lower ∧ (cell12902 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12902 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12902 ⟨17,by decide⟩).lower ∧ (cell12902 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12902 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12902 ⟨18,by decide⟩).lower ∧ (cell12902 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12902 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12902 ⟨19,by decide⟩).lower ∧ (cell12902 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12902 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12902 ⟨20,by decide⟩).lower ∧ (cell12902 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12902 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12902 ⟨21,by decide⟩).lower ∧ (cell12902 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12902 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12902 ⟨22,by decide⟩).lower ∧ (cell12902 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12902 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12902 ⟨23,by decide⟩).lower ∧ (cell12902 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12902 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12902 ⟨24,by decide⟩).lower ∧ (cell12902 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12902 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12902 ⟨25,by decide⟩).lower ∧ (cell12902 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12902 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12902 ⟨26,by decide⟩).lower ∧ (cell12902 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12902 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12902 ⟨27,by decide⟩).lower ∧ (cell12902 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12902 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12902 ⟨28,by decide⟩).lower ∧ (cell12902 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12902 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12902 ⟨29,by decide⟩).lower ∧ (cell12902 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12902 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12902 ⟨30,by decide⟩).lower ∧ (cell12902 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12902 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12902 ⟨31,by decide⟩).lower ∧ (cell12902 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12902 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12902 ⟨32,by decide⟩).lower ∧ (cell12902 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12902 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12902 ⟨33,by decide⟩).lower ∧ (cell12902 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12902 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12902 ⟨34,by decide⟩).lower ∧ (cell12902 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12902 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12902 ⟨35,by decide⟩).lower ∧ (cell12902 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12902 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12902 ⟨36,by decide⟩).lower ∧ (cell12902 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12902 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12902 ⟨37,by decide⟩).lower ∧ (cell12902 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12902 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12902 ⟨38,by decide⟩).lower ∧ (cell12902 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12902 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12902 ⟨39,by decide⟩).lower ∧ (cell12902 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12902 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12902 ⟨40,by decide⟩).lower ∧ (cell12902 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12902 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12902 ⟨41,by decide⟩).lower ∧ (cell12902 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12902 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12902 ⟨42,by decide⟩).lower ∧ (cell12902 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12902 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12902 ⟨43,by decide⟩).lower ∧ (cell12902 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12902 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12902 ⟨44,by decide⟩).lower ∧ (cell12902 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12902 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12902 ⟨45,by decide⟩).lower ∧ (cell12902 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12902 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12902 ⟨46,by decide⟩).lower ∧ (cell12902 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12902 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12902 ⟨47,by decide⟩).lower ∧ (cell12902 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12902 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12902 ⟨48,by decide⟩).lower ∧ (cell12902 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12902 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12902 ⟨49,by decide⟩).lower ∧ (cell12902 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12902 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12902 ⟨50,by decide⟩).lower ∧ (cell12902 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12902 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12902 ⟨51,by decide⟩).lower ∧ (cell12902 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12902 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12902 ⟨52,by decide⟩).lower ∧ (cell12902 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12902 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12902 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12902 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12902,cell12902,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12902 i).lower ∧
    (cell12902 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12902 i).upper ≤ (0.532 : ℝ) ∧
    (cell12902 i).centre ≤ (0.1 : ℝ) ∧ (cell12902 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12902 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12902 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12902

/-! The local source numeric instances at 12902 have no network premises. -/
namespace BstLean.Part269.N12902
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12902)
open BstLean.Part268 (cell12902)

noncomputable def sourceNumerics12902 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12902 (cell12902 i)
      scalarRow12902.M scalarRow12902.H scalarRow12902.xi := by
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
    energy_allowance := scalarRow12902.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12902]
    centre_nonneg := (scalarRow12902.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12902])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12902
/-! Actual 12903 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12903 ≤ (1.035523947272 : ℝ) := by
  have hr : (113.591372911854 : ℝ) ≤ √(12903 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.591372911854 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12903 12903 (11 / 1000) ≤
    (0.008415137055 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12903) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.591372911854 : ℝ) ≤ √(12903 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12903)
  have hdiv : K / √(12903 : ℝ) ≤ K / 113.591372911854 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.591372911854 ≤ (0.008415137055 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12903.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12903 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12903 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12903 := gPlus_lower 12903
end BstLean.Part269.N12903

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12903
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035523947271 : ℝ) ≤ wn 12903 := by
  have hn : √(12903 : ℝ) ≤ 113.591372911855 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12903 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.591372911855 ≤ 2 / √(12903 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247849804 : ℝ) ≤ rhoBar 12903 BstLean.Part154.csC ∧
    rhoBar 12903 BstLean.Part154.csC ≤ 0.000247850188 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035523947271 : ℝ) / (1.295212 * 12903) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035523947272 : ℝ) / (1.29521 * 12903) := by gcongr
      _ ≤ (0.000247850188 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12903 BstLean.Part154.csC) ≤ 0.000991462182 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12903 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) ≤ 0.000189309505 ∧
    cc1 (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) ≤ 0.000120458924 ∧
    cc2 (rhoBar 12903 BstLean.Part154.csC) ≤ 0.000069927363 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12903 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12903 BstLean.Part154.csC * nuR (rhoBar 12903 BstLean.Part154.csC)) ≤ 0.000495715734 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247850188 : ℝ) * 0.000991462182 := by gcongr
      _ ≤ (0.000495715734 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12903 BstLean.Part154.csC) * nuR (rhoBar 12903 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991462182 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12903 BstLean.Part154.csC) * rhoBar 12903 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247850188 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247850188 / 2 + 0.399 * 0.000991462182 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189309505 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495715734 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120458924 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247850188 / 1.414213562 := by gcongr
      _ ≤ (0.000069927363 : ℝ) := by norm_num

end BstLean.Part269.N12903

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12903
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) ≤ 1.54768E-7 := by
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12903 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12903 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189309505 : ℝ) ^ 2 + 0.000120458924 ^ 2 + 3 * 0.000069927363 ^ 2 +
        2 * 0.797885 * 0.000189309505 * 0.000120458924 + 2 * 0.000189309505 * 0.000069927363 +
        4 * 0.797885 * 0.000120458924 * 0.000069927363 := by gcongr
    _ ≤ (1.54768E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12903 BstLean.Part154.csC Θ ≤ 0.002586501465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12903 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12903 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035523947272 * 1.54768E-7 / (0.000247849804 : ℝ) := by gcongr
    _ ≤ 0.002586501465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12903 BstLean.Part154.csC Θ ≤ 0.002869065465 + 0.000653566231 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12903 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035523947272 : ℝ) * ((2 * Θ * 0.000247850188 +
        (6863 / 10000) * 0.000247850188 * 12903 * 0.000991462182) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002869065465 + 0.000653566231 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12903 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12903 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12903 0.011 Θ ∧ gammaRatio 12903 0.011 Θ ≤ 0.000085204486 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12903 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035523947272 : ℝ) * 0.525 / ((1 - 0.011) * 12903) := by gcongr
      _ ≤ (0.000085204486 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12903 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12903 0.011 Θ) :=
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
    badAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12903 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12903 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12903 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12903 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12903 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12903 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12903 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12903 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12903 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12903 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035523947272 : ℝ) * 12903 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003332736482 + 0.003240067696 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12903

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12903
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12903 BstLean.Part154.csC) (piBar (rhoBar 12903 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12903 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12903 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12903 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12903 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12903 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12903 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12903 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12903 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12903 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052065354973 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12903) ≤ 0.010513453183 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12903 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035523947272)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010513453183 + 2 * 0.737676 / 12903) := by gcongr
    _ ≤ (0.052065354973 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12903 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12903

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12903
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512604123 : ℝ) ≤ plow 12903 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12903) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540372023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357913270) : eMP 12903 0.011 xi bn ≤ 0.001169306454 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12903 : ℝ) * (1 - 0.011))) ≤ 0.000578185881 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357913270 / (12903 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578185881 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578185881 : ℝ) + 3.141593 * 0.052540372023 / (12903 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169306454 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540372023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357913270) : PiBarMP 12903 12 0.011 xi bn ≤ 0.159964844697 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12903 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036849874763 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.964892776472 : ℝ) ≤ √((12903 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.591372911854 : ℝ) ≤ √(12903 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12903) ≤ 0.122653753588 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036849874763 + 0.052540372023 * 1.772454 / (2 * (112.964892776472 : ℝ))) * (1 + 0.001169306454) +
        8 / (12903 * 113.591372911854) + 0.122653753588 := by gcongr
    _ ≤ (0.159964844697 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540372023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357913270) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281282221768) :
    parallelOracle 12903 0.011 xi bn cd ≤ 0.160939527689 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12903 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12903 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512604123 : ℝ) ≤ plow 12903 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.591372911854 : ℝ) ≤ √(12903 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281282221768 : ℝ) / (2 * 0.560512604123 * 113.591372911854)) * 0.159964844697 +
        0.281282221768 ^ 2 / (2 * 0.560512604123 * 113.591372911854) := by gcongr
    _ ≤ (0.160939527689 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052540372023) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357913270)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281282221768) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12903 12903 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512604123 : ℝ) ≤ plow 12903 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.591372911854 : ℝ) ≤ √(12903 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12903 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12903 Θ 1.22 ≤ 0.011674306473 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.591372911854 := by gcongr <;> linarith
      _ ≤ (0.011674306473 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12903 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12903 12903 0.011 ≤ 0.008415137055 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12903 12903 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12903 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12903 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12903 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12903 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160939527689 + 0.011674306473 + (0.008415137055 : ℝ) *
        (1 + 2 * (0.281282221768 + 0.011674306473) / (0.560512604123 * 113.591372911854))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12903]

end BstLean.Part269.N12903

/-! The original eight local profiles supply actual 12903 moment certificates. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12903 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052540372023 ∧
    0 ≤ bN 12903 BstLean.Part154.csC (groupTheta g) ∧ bN 12903 BstLean.Part154.csC (groupTheta g) ≤ 0.001357913270 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12903 12903 0.011
      (momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12903 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12903 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12903 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229216866795 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12903 0.011
      (momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12903 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12903
/-! The actual computed-centre upper energy formula at 12903. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12903

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12903)
open BstLean.Part268 (cell12903)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084919146778
  | 2 => 0.085851861065
  | 3 => 0.086781326190
  | 4 => 0.087708635282
  | 5 => 0.088635120419
  | 6 => 0.089562389361
  | 7 => 0.090492365976
  | 8 => 0.091427334440
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12903 12903 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12903 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12903

/-! Actual upper energy certificates on all 43 source endpoints at 12903. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12903)
open BstLean.Part268 (cell12903)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12903 (gMinus 12903) (1 - (cell12903 i).lower) ≤ 1 ∧
    energyUpper 12903 (gMinus 12903) (BstLean.Part211.gPlus 12903)
      (finiteEnergy 12903 12903 0.011) (1 - (cell12903 i).lower) ≤
      (cell12903 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨10,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨11,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨12,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨13,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨14,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨15,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨16,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨17,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨18,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨19,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨20,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨21,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨22,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨23,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨24,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨25,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨26,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨27,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨28,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨29,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨30,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨31,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨32,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨33,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨34,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨35,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨36,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨37,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨38,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨39,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨40,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨41,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨42,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨43,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨44,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨45,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨46,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨47,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨48,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨49,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨50,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨51,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12903) (by norm_num)
        (q := 1 - (cell12903 ⟨52,by decide⟩).lower)
        (by norm_num [cell12903]) (by norm_num [cell12903])
      exact ⟨E.1,E.2.trans (by norm_num [cell12903])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12903

/-! Source-cell containment and simple scalar guards at 12903. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12903)
open BstLean.Part268 (cell12903)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12903 ⟨10,by decide⟩).lower ∧ (cell12903 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12903 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12903 ⟨11,by decide⟩).lower ∧ (cell12903 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12903 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12903 ⟨12,by decide⟩).lower ∧ (cell12903 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12903 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12903 ⟨13,by decide⟩).lower ∧ (cell12903 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12903 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12903 ⟨14,by decide⟩).lower ∧ (cell12903 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12903 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12903 ⟨15,by decide⟩).lower ∧ (cell12903 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12903 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12903 ⟨16,by decide⟩).lower ∧ (cell12903 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12903 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12903 ⟨17,by decide⟩).lower ∧ (cell12903 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12903 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12903 ⟨18,by decide⟩).lower ∧ (cell12903 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12903 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12903 ⟨19,by decide⟩).lower ∧ (cell12903 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12903 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12903 ⟨20,by decide⟩).lower ∧ (cell12903 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12903 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12903 ⟨21,by decide⟩).lower ∧ (cell12903 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12903 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12903 ⟨22,by decide⟩).lower ∧ (cell12903 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12903 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12903 ⟨23,by decide⟩).lower ∧ (cell12903 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12903 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12903 ⟨24,by decide⟩).lower ∧ (cell12903 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12903 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12903 ⟨25,by decide⟩).lower ∧ (cell12903 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12903 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12903 ⟨26,by decide⟩).lower ∧ (cell12903 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12903 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12903 ⟨27,by decide⟩).lower ∧ (cell12903 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12903 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12903 ⟨28,by decide⟩).lower ∧ (cell12903 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12903 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12903 ⟨29,by decide⟩).lower ∧ (cell12903 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12903 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12903 ⟨30,by decide⟩).lower ∧ (cell12903 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12903 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12903 ⟨31,by decide⟩).lower ∧ (cell12903 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12903 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12903 ⟨32,by decide⟩).lower ∧ (cell12903 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12903 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12903 ⟨33,by decide⟩).lower ∧ (cell12903 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12903 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12903 ⟨34,by decide⟩).lower ∧ (cell12903 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12903 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12903 ⟨35,by decide⟩).lower ∧ (cell12903 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12903 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12903 ⟨36,by decide⟩).lower ∧ (cell12903 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12903 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12903 ⟨37,by decide⟩).lower ∧ (cell12903 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12903 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12903 ⟨38,by decide⟩).lower ∧ (cell12903 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12903 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12903 ⟨39,by decide⟩).lower ∧ (cell12903 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12903 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12903 ⟨40,by decide⟩).lower ∧ (cell12903 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12903 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12903 ⟨41,by decide⟩).lower ∧ (cell12903 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12903 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12903 ⟨42,by decide⟩).lower ∧ (cell12903 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12903 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12903 ⟨43,by decide⟩).lower ∧ (cell12903 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12903 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12903 ⟨44,by decide⟩).lower ∧ (cell12903 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12903 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12903 ⟨45,by decide⟩).lower ∧ (cell12903 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12903 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12903 ⟨46,by decide⟩).lower ∧ (cell12903 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12903 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12903 ⟨47,by decide⟩).lower ∧ (cell12903 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12903 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12903 ⟨48,by decide⟩).lower ∧ (cell12903 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12903 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12903 ⟨49,by decide⟩).lower ∧ (cell12903 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12903 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12903 ⟨50,by decide⟩).lower ∧ (cell12903 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12903 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12903 ⟨51,by decide⟩).lower ∧ (cell12903 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12903 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12903 ⟨52,by decide⟩).lower ∧ (cell12903 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12903 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12903 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12903 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12903,cell12903,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12903 i).lower ∧
    (cell12903 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12903 i).upper ≤ (0.532 : ℝ) ∧
    (cell12903 i).centre ≤ (0.1 : ℝ) ∧ (cell12903 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12903 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12903 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12903

/-! The local source numeric instances at 12903 have no network premises. -/
namespace BstLean.Part269.N12903
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12903)
open BstLean.Part268 (cell12903)

noncomputable def sourceNumerics12903 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12903 (cell12903 i)
      scalarRow12903.M scalarRow12903.H scalarRow12903.xi := by
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
    energy_allowance := scalarRow12903.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12903]
    centre_nonneg := (scalarRow12903.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12903])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12903
/-! Actual 12904 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12904 ≤ (1.035522558763 : ℝ) := by
  have hr : (113.595774569303 : ℝ) ≤ √(12904 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.595774569303 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12904 12904 (11 / 1000) ≤
    (0.008414810979 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12904) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.595774569303 : ℝ) ≤ √(12904 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12904)
  have hdiv : K / √(12904 : ℝ) ≤ K / 113.595774569303 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.595774569303 ≤ (0.008414810979 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12904.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12904 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12904 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12904 := gPlus_lower 12904
end BstLean.Part269.N12904

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12904
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035522558762 : ℝ) ≤ wn 12904 := by
  have hn : √(12904 : ℝ) ≤ 113.595774569304 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12904 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.595774569304 ≤ 2 / √(12904 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247830265 : ℝ) ≤ rhoBar 12904 BstLean.Part154.csC ∧
    rhoBar 12904 BstLean.Part154.csC ≤ 0.000247830649 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035522558762 : ℝ) / (1.295212 * 12904) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035522558763 : ℝ) / (1.29521 * 12904) := by gcongr
      _ ≤ (0.000247830649 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12904 BstLean.Part154.csC) ≤ 0.000991384017 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12904 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) ≤ 0.000189294580 ∧
    cc1 (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) ≤ 0.000120449427 ∧
    cc2 (rhoBar 12904 BstLean.Part154.csC) ≤ 0.000069921851 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12904 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12904 BstLean.Part154.csC * nuR (rhoBar 12904 BstLean.Part154.csC)) ≤ 0.000495676654 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247830649 : ℝ) * 0.000991384017 := by gcongr
      _ ≤ (0.000495676654 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12904 BstLean.Part154.csC) * nuR (rhoBar 12904 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991384017 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12904 BstLean.Part154.csC) * rhoBar 12904 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247830649 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247830649 / 2 + 0.399 * 0.000991384017 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189294580 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495676654 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120449427 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247830649 / 1.414213562 := by gcongr
      _ ≤ (0.000069921851 : ℝ) := by norm_num

end BstLean.Part269.N12904

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12904
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) ≤ 1.54743E-7 := by
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12904 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12904 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189294580 : ℝ) ^ 2 + 0.000120449427 ^ 2 + 3 * 0.000069921851 ^ 2 +
        2 * 0.797885 * 0.000189294580 * 0.000120449427 + 2 * 0.000189294580 * 0.000069921851 +
        4 * 0.797885 * 0.000120449427 * 0.000069921851 := by gcongr
    _ ≤ (1.54743E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12904 BstLean.Part154.csC Θ ≤ 0.002586284082 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12904 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12904 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035522558763 * 1.54743E-7 / (0.000247830265 : ℝ) := by gcongr
    _ ≤ 0.002586284082 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12904 BstLean.Part154.csC Θ ≤ 0.002868831586 + 0.000653513831 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12904 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035522558763 : ℝ) * ((2 * Θ * 0.000247830649 +
        (6863 / 10000) * 0.000247830649 * 12904 * 0.000991384017) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002868831586 + 0.000653513831 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12904 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12904 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12904 0.011 Θ ∧ gammaRatio 12904 0.011 Θ ≤ 0.000085197769 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12904 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035522558763 : ℝ) * 0.525 / ((1 - 0.011) * 12904) := by gcongr
      _ ≤ (0.000085197769 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12904 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12904 0.011 Θ) :=
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
    badAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12904 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12904 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12904 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12904 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12904 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12904 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12904 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12904 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12904 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12904 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035522558763 : ℝ) * 12904 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003332502603 + 0.003239797913 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12904

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12904
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12904 BstLean.Part154.csC) (piBar (rhoBar 12904 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12904 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12904 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12904 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12904 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12904 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12904 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12904 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12904 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12904 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052063315817 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12904) ≤ 0.010513045803 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12904 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035522558763)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010513045803 + 2 * 0.737676 / 12904) := by gcongr
    _ ≤ (0.052063315817 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12904 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12904

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12904
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512647930 : ℝ) ≤ plow 12904 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12904) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539996508)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357799144) : eMP 12904 0.011 xi bn ≤ 0.001169211959 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12904 : ℝ) * (1 - 0.011))) ≤ 0.000578139181 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357799144 / (12904 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578139181 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578139181 : ℝ) + 3.141593 * 0.052539996508 / (12904 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169211959 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539996508)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357799144) : PiBarMP 12904 12 0.011 xi bn ≤ 0.159958518592 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12904 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036848326204 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.969270157861 : ℝ) ≤ √((12904 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.595774569303 : ℝ) ≤ √(12904 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12904) ≤ 0.122649000948 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036848326204 + 0.052539996508 * 1.772454 / (2 * (112.969270157861 : ℝ))) * (1 + 0.001169211959) +
        8 / (12904 * 113.595774569303) + 0.122649000948 := by gcongr
    _ ≤ (0.159958518592 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539996508)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357799144) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281279363484) :
    parallelOracle 12904 0.011 xi bn cd ≤ 0.160933133550 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12904 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12904 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512647930 : ℝ) ≤ plow 12904 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.595774569303 : ℝ) ≤ √(12904 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281279363484 : ℝ) / (2 * 0.560512647930 * 113.595774569303)) * 0.159958518592 +
        0.281279363484 ^ 2 / (2 * 0.560512647930 * 113.595774569303) := by gcongr
    _ ≤ (0.160933133550 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539996508) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357799144)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281279363484) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12904 12904 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512647930 : ℝ) ≤ plow 12904 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.595774569303 : ℝ) ≤ √(12904 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12904 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12904 Θ 1.22 ≤ 0.011673854112 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.595774569303 := by gcongr <;> linarith
      _ ≤ (0.011673854112 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12904 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12904 12904 0.011 ≤ 0.008414810979 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12904 12904 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12904 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12904 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12904 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12904 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160933133550 + 0.011673854112 + (0.008414810979 : ℝ) *
        (1 + 2 * (0.281279363484 + 0.011673854112) / (0.560512647930 * 113.595774569303))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12904]

end BstLean.Part269.N12904

/-! The original eight local profiles supply actual 12904 moment certificates. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12904 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052539996508 ∧
    0 ≤ bN 12904 BstLean.Part154.csC (groupTheta g) ∧ bN 12904 BstLean.Part154.csC (groupTheta g) ≤ 0.001357799144 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12904 12904 0.011
      (momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12904 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12904 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12904 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229216047667 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12904 0.011
      (momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12904 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12904
/-! The actual computed-centre upper energy formula at 12904. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12904

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12904)
open BstLean.Part268 (cell12904)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084916430193
  | 2 => 0.085849098864
  | 3 => 0.086778512427
  | 4 => 0.087705762600
  | 5 => 0.088632179788
  | 6 => 0.089559369785
  | 7 => 0.090489254171
  | 8 => 0.091424114468
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12904 12904 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12904 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12904

/-! Actual upper energy certificates on all 43 source endpoints at 12904. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12904)
open BstLean.Part268 (cell12904)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12904 (gMinus 12904) (1 - (cell12904 i).lower) ≤ 1 ∧
    energyUpper 12904 (gMinus 12904) (BstLean.Part211.gPlus 12904)
      (finiteEnergy 12904 12904 0.011) (1 - (cell12904 i).lower) ≤
      (cell12904 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨10,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨11,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨12,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨13,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨14,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨15,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨16,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨17,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨18,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨19,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨20,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨21,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨22,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨23,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨24,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨25,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨26,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨27,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨28,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨29,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨30,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨31,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨32,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨33,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨34,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨35,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨36,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨37,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨38,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨39,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨40,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨41,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨42,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨43,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨44,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨45,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨46,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨47,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨48,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨49,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨50,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨51,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12904) (by norm_num)
        (q := 1 - (cell12904 ⟨52,by decide⟩).lower)
        (by norm_num [cell12904]) (by norm_num [cell12904])
      exact ⟨E.1,E.2.trans (by norm_num [cell12904])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12904

/-! Source-cell containment and simple scalar guards at 12904. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12904)
open BstLean.Part268 (cell12904)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12904 ⟨10,by decide⟩).lower ∧ (cell12904 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12904 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12904 ⟨11,by decide⟩).lower ∧ (cell12904 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12904 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12904 ⟨12,by decide⟩).lower ∧ (cell12904 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12904 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12904 ⟨13,by decide⟩).lower ∧ (cell12904 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12904 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12904 ⟨14,by decide⟩).lower ∧ (cell12904 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12904 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12904 ⟨15,by decide⟩).lower ∧ (cell12904 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12904 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12904 ⟨16,by decide⟩).lower ∧ (cell12904 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12904 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12904 ⟨17,by decide⟩).lower ∧ (cell12904 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12904 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12904 ⟨18,by decide⟩).lower ∧ (cell12904 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12904 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12904 ⟨19,by decide⟩).lower ∧ (cell12904 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12904 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12904 ⟨20,by decide⟩).lower ∧ (cell12904 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12904 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12904 ⟨21,by decide⟩).lower ∧ (cell12904 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12904 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12904 ⟨22,by decide⟩).lower ∧ (cell12904 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12904 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12904 ⟨23,by decide⟩).lower ∧ (cell12904 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12904 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12904 ⟨24,by decide⟩).lower ∧ (cell12904 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12904 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12904 ⟨25,by decide⟩).lower ∧ (cell12904 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12904 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12904 ⟨26,by decide⟩).lower ∧ (cell12904 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12904 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12904 ⟨27,by decide⟩).lower ∧ (cell12904 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12904 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12904 ⟨28,by decide⟩).lower ∧ (cell12904 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12904 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12904 ⟨29,by decide⟩).lower ∧ (cell12904 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12904 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12904 ⟨30,by decide⟩).lower ∧ (cell12904 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12904 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12904 ⟨31,by decide⟩).lower ∧ (cell12904 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12904 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12904 ⟨32,by decide⟩).lower ∧ (cell12904 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12904 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12904 ⟨33,by decide⟩).lower ∧ (cell12904 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12904 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12904 ⟨34,by decide⟩).lower ∧ (cell12904 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12904 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12904 ⟨35,by decide⟩).lower ∧ (cell12904 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12904 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12904 ⟨36,by decide⟩).lower ∧ (cell12904 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12904 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12904 ⟨37,by decide⟩).lower ∧ (cell12904 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12904 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12904 ⟨38,by decide⟩).lower ∧ (cell12904 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12904 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12904 ⟨39,by decide⟩).lower ∧ (cell12904 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12904 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12904 ⟨40,by decide⟩).lower ∧ (cell12904 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12904 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12904 ⟨41,by decide⟩).lower ∧ (cell12904 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12904 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12904 ⟨42,by decide⟩).lower ∧ (cell12904 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12904 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12904 ⟨43,by decide⟩).lower ∧ (cell12904 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12904 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12904 ⟨44,by decide⟩).lower ∧ (cell12904 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12904 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12904 ⟨45,by decide⟩).lower ∧ (cell12904 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12904 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12904 ⟨46,by decide⟩).lower ∧ (cell12904 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12904 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12904 ⟨47,by decide⟩).lower ∧ (cell12904 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12904 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12904 ⟨48,by decide⟩).lower ∧ (cell12904 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12904 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12904 ⟨49,by decide⟩).lower ∧ (cell12904 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12904 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12904 ⟨50,by decide⟩).lower ∧ (cell12904 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12904 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12904 ⟨51,by decide⟩).lower ∧ (cell12904 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12904 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12904 ⟨52,by decide⟩).lower ∧ (cell12904 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12904 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12904 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12904 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12904,cell12904,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12904 i).lower ∧
    (cell12904 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12904 i).upper ≤ (0.532 : ℝ) ∧
    (cell12904 i).centre ≤ (0.1 : ℝ) ∧ (cell12904 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12904 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12904 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12904

/-! The local source numeric instances at 12904 have no network premises. -/
namespace BstLean.Part269.N12904
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12904)
open BstLean.Part268 (cell12904)

noncomputable def sourceNumerics12904 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12904 (cell12904 i)
      scalarRow12904.M scalarRow12904.H scalarRow12904.xi := by
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
    energy_allowance := scalarRow12904.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12904]
    centre_nonneg := (scalarRow12904.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12904])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12904
/-! Actual 12905 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12905 ≤ (1.035521170417 : ℝ) := by
  have hr : (113.600176056201 : ℝ) ≤ √(12905 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.600176056201 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12905 12905 (11 / 1000) ≤
    (0.008414484941 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12905) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.600176056201 : ℝ) ≤ √(12905 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12905)
  have hdiv : K / √(12905 : ℝ) ≤ K / 113.600176056201 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.600176056201 ≤ (0.008414484941 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12905.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12905 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12905 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12905 := gPlus_lower 12905
end BstLean.Part269.N12905

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12905
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035521170416 : ℝ) ≤ wn 12905 := by
  have hn : √(12905 : ℝ) ≤ 113.600176056202 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12905 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.600176056202 ≤ 2 / √(12905 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247810728 : ℝ) ≤ rhoBar 12905 BstLean.Part154.csC ∧
    rhoBar 12905 BstLean.Part154.csC ≤ 0.000247811112 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035521170416 : ℝ) / (1.295212 * 12905) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035521170417 : ℝ) / (1.29521 * 12905) := by gcongr
      _ ≤ (0.000247811112 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12905 BstLean.Part154.csC) ≤ 0.000991305859 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12905 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) ≤ 0.000189279657 ∧
    cc1 (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) ≤ 0.000120439932 ∧
    cc2 (rhoBar 12905 BstLean.Part154.csC) ≤ 0.000069916339 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12905 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12905 BstLean.Part154.csC * nuR (rhoBar 12905 BstLean.Part154.csC)) ≤ 0.000495637577 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247811112 : ℝ) * 0.000991305859 := by gcongr
      _ ≤ (0.000495637577 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12905 BstLean.Part154.csC) * nuR (rhoBar 12905 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991305859 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12905 BstLean.Part154.csC) * rhoBar 12905 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247811112 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247811112 / 2 + 0.399 * 0.000991305859 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189279657 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495637577 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120439932 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247811112 / 1.414213562 := by gcongr
      _ ≤ (0.000069916339 : ℝ) := by norm_num

end BstLean.Part269.N12905

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12905
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) ≤ 1.54719E-7 := by
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12905 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12905 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189279657 : ℝ) ^ 2 + 0.000120439932 ^ 2 + 3 * 0.000069916339 ^ 2 +
        2 * 0.797885 * 0.000189279657 * 0.000120439932 + 2 * 0.000189279657 * 0.000069916339 +
        4 * 0.797885 * 0.000120439932 * 0.000069916339 := by gcongr
    _ ≤ (1.54719E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12905 BstLean.Part154.csC Θ ≤ 0.002586083360 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12905 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12905 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035521170417 * 1.54719E-7 / (0.000247810728 : ℝ) := by gcongr
    _ ≤ 0.002586083360 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12905 BstLean.Part154.csC Θ ≤ 0.002868597717 + 0.000653461437 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12905 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035521170417 : ℝ) * ((2 * Θ * 0.000247811112 +
        (6863 / 10000) * 0.000247811112 * 12905 * 0.000991305859) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002868597717 + 0.000653461437 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12905 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12905 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12905 0.011 Θ ∧ gammaRatio 12905 0.011 Θ ≤ 0.000085191052 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12905 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035521170417 : ℝ) * 0.525 / ((1 - 0.011) * 12905) := by gcongr
      _ ≤ (0.000085191052 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12905 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12905 0.011 Θ) :=
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
    badAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12905 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12905 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12905 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12905 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12905 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12905 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12905 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12905 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12905 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12905 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035521170417 : ℝ) * 12905 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003332268734 + 0.003239544797 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12905

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12905
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12905 BstLean.Part154.csC) (piBar (rhoBar 12905 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12905 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12905 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12905 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12905 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12905 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12905 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12905 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12905 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12905 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052061276903 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12905) ≤ 0.010512638471 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12905 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035521170417)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010512638471 + 2 * 0.737676 / 12905) := by gcongr
    _ ≤ (0.052061276903 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12905 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12905

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12905
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512691731 : ℝ) ≤ plow 12905 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12905) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539629753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357693764) : eMP 12905 0.011 xi bn ≤ 0.001169121197 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12905 : ℝ) * (1 - 0.011))) ≤ 0.000578094346 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357693764 / (12905 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578094346 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578094346 : ℝ) + 3.141593 * 0.052539629753 / (12905 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169121197 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539629753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357693764) : PiBarMP 12905 12 0.011 xi bn ≤ 0.159952312004 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12905 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036846896261 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.973647369641 : ℝ) ≤ √((12905 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.600176056201 : ℝ) ≤ √(12905 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12905) ≤ 0.122644248860 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036846896261 + 0.052539629753 * 1.772454 / (2 * (112.973647369641 : ℝ))) * (1 + 0.001169121197) +
        8 / (12905 * 113.600176056201) + 0.122644248860 := by gcongr
    _ ≤ (0.159952312004 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539629753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357693764) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281276524549) :
    parallelOracle 12905 0.011 xi bn cd ≤ 0.160926859309 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12905 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12905 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512691731 : ℝ) ≤ plow 12905 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.600176056201 : ℝ) ≤ √(12905 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281276524549 : ℝ) / (2 * 0.560512691731 * 113.600176056201)) * 0.159952312004 +
        0.281276524549 ^ 2 / (2 * 0.560512691731 * 113.600176056201) := by gcongr
    _ ≤ (0.160926859309 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539629753) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357693764)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281276524549) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12905 12905 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512691731 : ℝ) ≤ plow 12905 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.600176056201 : ℝ) ≤ √(12905 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12905 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12905 Θ 1.22 ≤ 0.011673401804 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.600176056201 := by gcongr <;> linarith
      _ ≤ (0.011673401804 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12905 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12905 12905 0.011 ≤ 0.008414484941 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12905 12905 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12905 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12905 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12905 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12905 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160926859309 + 0.011673401804 + (0.008414484941 : ℝ) *
        (1 + 2 * (0.281276524549 + 0.011673401804) / (0.560512691731 * 113.600176056201))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12905]

end BstLean.Part269.N12905

/-! The original eight local profiles supply actual 12905 moment certificates. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12905 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052539629753 ∧
    0 ≤ bN 12905 BstLean.Part154.csC (groupTheta g) ∧ bN 12905 BstLean.Part154.csC (groupTheta g) ≤ 0.001357693764 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12905 12905 0.011
      (momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12905 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12905 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12905 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229215247646 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12905 0.011
      (momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12905 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12905
/-! The actual computed-centre upper energy formula at 12905. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12905

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12905)
open BstLean.Part268 (cell12905)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084913714496
  | 2 => 0.085846337583
  | 3 => 0.086775699628
  | 4 => 0.087702890934
  | 5 => 0.088629240235
  | 6 => 0.089556351366
  | 7 => 0.090486143617
  | 8 => 0.091420895859
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12905 12905 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12905 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12905

/-! Actual upper energy certificates on all 43 source endpoints at 12905. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12905)
open BstLean.Part268 (cell12905)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12905 (gMinus 12905) (1 - (cell12905 i).lower) ≤ 1 ∧
    energyUpper 12905 (gMinus 12905) (BstLean.Part211.gPlus 12905)
      (finiteEnergy 12905 12905 0.011) (1 - (cell12905 i).lower) ≤
      (cell12905 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨10,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨11,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨12,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨13,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨14,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨15,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨16,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨17,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨18,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨19,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨20,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨21,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨22,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨23,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨24,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨25,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨26,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨27,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨28,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨29,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨30,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨31,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨32,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨33,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨34,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨35,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨36,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨37,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨38,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨39,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨40,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨41,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨42,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨43,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨44,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨45,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨46,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨47,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨48,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨49,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨50,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨51,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12905) (by norm_num)
        (q := 1 - (cell12905 ⟨52,by decide⟩).lower)
        (by norm_num [cell12905]) (by norm_num [cell12905])
      exact ⟨E.1,E.2.trans (by norm_num [cell12905])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12905

/-! Source-cell containment and simple scalar guards at 12905. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12905)
open BstLean.Part268 (cell12905)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12905 ⟨10,by decide⟩).lower ∧ (cell12905 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12905 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12905 ⟨11,by decide⟩).lower ∧ (cell12905 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12905 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12905 ⟨12,by decide⟩).lower ∧ (cell12905 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12905 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12905 ⟨13,by decide⟩).lower ∧ (cell12905 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12905 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12905 ⟨14,by decide⟩).lower ∧ (cell12905 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12905 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12905 ⟨15,by decide⟩).lower ∧ (cell12905 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12905 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12905 ⟨16,by decide⟩).lower ∧ (cell12905 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12905 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12905 ⟨17,by decide⟩).lower ∧ (cell12905 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12905 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12905 ⟨18,by decide⟩).lower ∧ (cell12905 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12905 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12905 ⟨19,by decide⟩).lower ∧ (cell12905 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12905 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12905 ⟨20,by decide⟩).lower ∧ (cell12905 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12905 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12905 ⟨21,by decide⟩).lower ∧ (cell12905 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12905 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12905 ⟨22,by decide⟩).lower ∧ (cell12905 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12905 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12905 ⟨23,by decide⟩).lower ∧ (cell12905 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12905 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12905 ⟨24,by decide⟩).lower ∧ (cell12905 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12905 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12905 ⟨25,by decide⟩).lower ∧ (cell12905 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12905 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12905 ⟨26,by decide⟩).lower ∧ (cell12905 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12905 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12905 ⟨27,by decide⟩).lower ∧ (cell12905 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12905 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12905 ⟨28,by decide⟩).lower ∧ (cell12905 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12905 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12905 ⟨29,by decide⟩).lower ∧ (cell12905 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12905 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12905 ⟨30,by decide⟩).lower ∧ (cell12905 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12905 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12905 ⟨31,by decide⟩).lower ∧ (cell12905 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12905 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12905 ⟨32,by decide⟩).lower ∧ (cell12905 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12905 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12905 ⟨33,by decide⟩).lower ∧ (cell12905 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12905 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12905 ⟨34,by decide⟩).lower ∧ (cell12905 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12905 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12905 ⟨35,by decide⟩).lower ∧ (cell12905 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12905 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12905 ⟨36,by decide⟩).lower ∧ (cell12905 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12905 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12905 ⟨37,by decide⟩).lower ∧ (cell12905 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12905 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12905 ⟨38,by decide⟩).lower ∧ (cell12905 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12905 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12905 ⟨39,by decide⟩).lower ∧ (cell12905 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12905 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12905 ⟨40,by decide⟩).lower ∧ (cell12905 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12905 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12905 ⟨41,by decide⟩).lower ∧ (cell12905 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12905 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12905 ⟨42,by decide⟩).lower ∧ (cell12905 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12905 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12905 ⟨43,by decide⟩).lower ∧ (cell12905 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12905 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12905 ⟨44,by decide⟩).lower ∧ (cell12905 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12905 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12905 ⟨45,by decide⟩).lower ∧ (cell12905 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12905 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12905 ⟨46,by decide⟩).lower ∧ (cell12905 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12905 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12905 ⟨47,by decide⟩).lower ∧ (cell12905 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12905 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12905 ⟨48,by decide⟩).lower ∧ (cell12905 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12905 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12905 ⟨49,by decide⟩).lower ∧ (cell12905 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12905 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12905 ⟨50,by decide⟩).lower ∧ (cell12905 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12905 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12905 ⟨51,by decide⟩).lower ∧ (cell12905 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12905 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12905 ⟨52,by decide⟩).lower ∧ (cell12905 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12905 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12905 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12905 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12905,cell12905,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12905 i).lower ∧
    (cell12905 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12905 i).upper ≤ (0.532 : ℝ) ∧
    (cell12905 i).centre ≤ (0.1 : ℝ) ∧ (cell12905 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12905 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12905 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12905

/-! The local source numeric instances at 12905 have no network premises. -/
namespace BstLean.Part269.N12905
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12905)
open BstLean.Part268 (cell12905)

noncomputable def sourceNumerics12905 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12905 (cell12905 i)
      scalarRow12905.M scalarRow12905.H scalarRow12905.xi := by
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
    energy_allowance := scalarRow12905.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12905]
    centre_nonneg := (scalarRow12905.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12905])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12905
/-! Actual 12906 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12906 ≤ (1.035519782233 : ℝ) := by
  have hr : (113.604577372568 : ℝ) ≤ √(12906 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.604577372568 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12906 12906 (11 / 1000) ≤
    (0.008414158941 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12906) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.604577372568 : ℝ) ≤ √(12906 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12906)
  have hdiv : K / √(12906 : ℝ) ≤ K / 113.604577372568 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.604577372568 ≤ (0.008414158941 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12906.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12906 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12906 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12906 := gPlus_lower 12906
end BstLean.Part269.N12906

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12906
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035519782232 : ℝ) ≤ wn 12906 := by
  have hn : √(12906 : ℝ) ≤ 113.604577372569 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12906 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.604577372569 ≤ 2 / √(12906 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247791195 : ℝ) ≤ rhoBar 12906 BstLean.Part154.csC ∧
    rhoBar 12906 BstLean.Part154.csC ≤ 0.000247791579 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035519782232 : ℝ) / (1.295212 * 12906) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035519782233 : ℝ) / (1.29521 * 12906) := by gcongr
      _ ≤ (0.000247791579 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12906 BstLean.Part154.csC) ≤ 0.000991227717 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12906 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) ≤ 0.000189264737 ∧
    cc1 (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) ≤ 0.000120430438 ∧
    cc2 (rhoBar 12906 BstLean.Part154.csC) ≤ 0.000069910828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12906 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12906 BstLean.Part154.csC * nuR (rhoBar 12906 BstLean.Part154.csC)) ≤ 0.000495598509 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247791579 : ℝ) * 0.000991227717 := by gcongr
      _ ≤ (0.000495598509 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12906 BstLean.Part154.csC) * nuR (rhoBar 12906 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991227717 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12906 BstLean.Part154.csC) * rhoBar 12906 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247791579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247791579 / 2 + 0.399 * 0.000991227717 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189264737 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495598509 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120430438 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247791579 / 1.414213562 := by gcongr
      _ ≤ (0.000069910828 : ℝ) := by norm_num

end BstLean.Part269.N12906

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12906
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) ≤ 1.54695E-7 := by
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12906 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12906 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189264737 : ℝ) ^ 2 + 0.000120430438 ^ 2 + 3 * 0.000069910828 ^ 2 +
        2 * 0.797885 * 0.000189264737 * 0.000120430438 + 2 * 0.000189264737 * 0.000069910828 +
        4 * 0.797885 * 0.000120430438 * 0.000069910828 := by gcongr
    _ ≤ (1.54695E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12906 BstLean.Part154.csC Θ ≤ 0.002585882565 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12906 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12906 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035519782233 * 1.54695E-7 / (0.000247791195 : ℝ) := by gcongr
    _ ≤ 0.002585882565 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12906 BstLean.Part154.csC Θ ≤ 0.002868363908 + 0.000653409054 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12906 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035519782233 : ℝ) * ((2 * Θ * 0.000247791579 +
        (6863 / 10000) * 0.000247791579 * 12906 * 0.000991227717) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002868363908 + 0.000653409054 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12906 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12906 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12906 0.011 Θ ∧ gammaRatio 12906 0.011 Θ ≤ 0.000085184337 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12906 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035519782233 : ℝ) * 0.525 / ((1 - 0.011) * 12906) := by gcongr
      _ ≤ (0.000085184337 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12906 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12906 0.011 Θ) :=
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
    badAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12906 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12906 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12906 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12906 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12906 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12906 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12906 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12906 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12906 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12906 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035519782233 : ℝ) * 12906 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003332034925 + 0.003239291619 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12906

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12906
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12906 BstLean.Part154.csC) (piBar (rhoBar 12906 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12906 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12906 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12906 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12906 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12906 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12906 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12906 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12906 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12906 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052059238226 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12906) ≤ 0.010512231186 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12906 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035519782233)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010512231186 + 2 * 0.737676 / 12906) := by gcongr
    _ ≤ (0.052059238226 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12906 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12906

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12906
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512735526 : ℝ) ≤ plow 12906 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12906) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539263025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357588347) : eMP 12906 0.011 xi bn ≤ 0.001169030426 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12906 : ℝ) * (1 - 0.011))) ≤ 0.000578049507 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357588347 / (12906 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578049507 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578049507 : ℝ) + 3.141593 * 0.052539263025 / (12906 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169030426 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539263025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357588347) : PiBarMP 12906 12 0.011 xi bn ≤ 0.159946105413 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12906 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036845465760 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.978024411829 : ℝ) ≤ √((12906 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.604577372568 : ℝ) ≤ √(12906 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12906) ≤ 0.122639497325 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036845465760 + 0.052539263025 * 1.772454 / (2 * (112.978024411829 : ℝ))) * (1 + 0.001169030426) +
        8 / (12906 * 113.604577372568) + 0.122639497325 := by gcongr
    _ ≤ (0.159946105413 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539263025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357588347) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281273685906) :
    parallelOracle 12906 0.011 xi bn cd ≤ 0.160920585073 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12906 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12906 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512735526 : ℝ) ≤ plow 12906 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.604577372568 : ℝ) ≤ √(12906 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281273685906 : ℝ) / (2 * 0.560512735526 * 113.604577372568)) * 0.159946105413 +
        0.281273685906 ^ 2 / (2 * 0.560512735526 * 113.604577372568) := by gcongr
    _ ≤ (0.160920585073 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052539263025) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357588347)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281273685906) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12906 12906 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512735526 : ℝ) ≤ plow 12906 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.604577372568 : ℝ) ≤ √(12906 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12906 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12906 Θ 1.22 ≤ 0.011672949548 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.604577372568 := by gcongr <;> linarith
      _ ≤ (0.011672949548 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12906 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12906 12906 0.011 ≤ 0.008414158941 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12906 12906 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12906 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12906 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12906 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12906 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160920585073 + 0.011672949548 + (0.008414158941 : ℝ) *
        (1 + 2 * (0.281273685906 + 0.011672949548) / (0.560512735526 * 113.604577372568))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12906]

end BstLean.Part269.N12906

/-! The original eight local profiles supply actual 12906 moment certificates. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12906 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052539263025 ∧
    0 ≤ bN 12906 BstLean.Part154.csC (groupTheta g) ∧ bN 12906 BstLean.Part154.csC (groupTheta g) ≤ 0.001357588347 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12906 12906 0.011
      (momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12906 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12906 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12906 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229214447680 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12906 0.011
      (momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12906 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12906
/-! The actual computed-centre upper energy formula at 12906. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12906

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12906)
open BstLean.Part268 (cell12906)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084910999684
  | 2 => 0.085843577222
  | 3 => 0.086772887791
  | 4 => 0.087700020281
  | 5 => 0.088626301760
  | 6 => 0.089553334102
  | 7 => 0.090483034312
  | 8 => 0.091417678613
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12906 12906 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12906 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12906

/-! Actual upper energy certificates on all 43 source endpoints at 12906. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12906)
open BstLean.Part268 (cell12906)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12906 (gMinus 12906) (1 - (cell12906 i).lower) ≤ 1 ∧
    energyUpper 12906 (gMinus 12906) (BstLean.Part211.gPlus 12906)
      (finiteEnergy 12906 12906 0.011) (1 - (cell12906 i).lower) ≤
      (cell12906 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨10,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨11,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨12,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨13,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨14,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨15,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨16,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨17,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨18,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨19,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨20,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨21,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨22,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨23,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨24,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨25,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨26,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨27,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨28,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨29,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨30,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨31,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨32,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨33,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨34,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨35,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨36,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨37,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨38,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨39,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨40,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨41,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨42,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨43,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨44,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨45,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨46,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨47,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨48,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨49,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨50,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨51,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12906) (by norm_num)
        (q := 1 - (cell12906 ⟨52,by decide⟩).lower)
        (by norm_num [cell12906]) (by norm_num [cell12906])
      exact ⟨E.1,E.2.trans (by norm_num [cell12906])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12906

/-! Source-cell containment and simple scalar guards at 12906. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12906)
open BstLean.Part268 (cell12906)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12906 ⟨10,by decide⟩).lower ∧ (cell12906 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12906 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12906 ⟨11,by decide⟩).lower ∧ (cell12906 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12906 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12906 ⟨12,by decide⟩).lower ∧ (cell12906 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12906 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12906 ⟨13,by decide⟩).lower ∧ (cell12906 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12906 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12906 ⟨14,by decide⟩).lower ∧ (cell12906 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12906 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12906 ⟨15,by decide⟩).lower ∧ (cell12906 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12906 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12906 ⟨16,by decide⟩).lower ∧ (cell12906 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12906 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12906 ⟨17,by decide⟩).lower ∧ (cell12906 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12906 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12906 ⟨18,by decide⟩).lower ∧ (cell12906 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12906 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12906 ⟨19,by decide⟩).lower ∧ (cell12906 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12906 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12906 ⟨20,by decide⟩).lower ∧ (cell12906 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12906 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12906 ⟨21,by decide⟩).lower ∧ (cell12906 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12906 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12906 ⟨22,by decide⟩).lower ∧ (cell12906 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12906 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12906 ⟨23,by decide⟩).lower ∧ (cell12906 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12906 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12906 ⟨24,by decide⟩).lower ∧ (cell12906 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12906 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12906 ⟨25,by decide⟩).lower ∧ (cell12906 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12906 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12906 ⟨26,by decide⟩).lower ∧ (cell12906 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12906 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12906 ⟨27,by decide⟩).lower ∧ (cell12906 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12906 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12906 ⟨28,by decide⟩).lower ∧ (cell12906 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12906 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12906 ⟨29,by decide⟩).lower ∧ (cell12906 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12906 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12906 ⟨30,by decide⟩).lower ∧ (cell12906 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12906 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12906 ⟨31,by decide⟩).lower ∧ (cell12906 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12906 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12906 ⟨32,by decide⟩).lower ∧ (cell12906 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12906 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12906 ⟨33,by decide⟩).lower ∧ (cell12906 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12906 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12906 ⟨34,by decide⟩).lower ∧ (cell12906 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12906 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12906 ⟨35,by decide⟩).lower ∧ (cell12906 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12906 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12906 ⟨36,by decide⟩).lower ∧ (cell12906 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12906 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12906 ⟨37,by decide⟩).lower ∧ (cell12906 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12906 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12906 ⟨38,by decide⟩).lower ∧ (cell12906 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12906 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12906 ⟨39,by decide⟩).lower ∧ (cell12906 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12906 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12906 ⟨40,by decide⟩).lower ∧ (cell12906 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12906 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12906 ⟨41,by decide⟩).lower ∧ (cell12906 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12906 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12906 ⟨42,by decide⟩).lower ∧ (cell12906 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12906 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12906 ⟨43,by decide⟩).lower ∧ (cell12906 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12906 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12906 ⟨44,by decide⟩).lower ∧ (cell12906 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12906 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12906 ⟨45,by decide⟩).lower ∧ (cell12906 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12906 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12906 ⟨46,by decide⟩).lower ∧ (cell12906 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12906 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12906 ⟨47,by decide⟩).lower ∧ (cell12906 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12906 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12906 ⟨48,by decide⟩).lower ∧ (cell12906 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12906 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12906 ⟨49,by decide⟩).lower ∧ (cell12906 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12906 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12906 ⟨50,by decide⟩).lower ∧ (cell12906 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12906 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12906 ⟨51,by decide⟩).lower ∧ (cell12906 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12906 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12906 ⟨52,by decide⟩).lower ∧ (cell12906 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12906 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12906 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12906 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12906,cell12906,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12906 i).lower ∧
    (cell12906 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12906 i).upper ≤ (0.532 : ℝ) ∧
    (cell12906 i).centre ≤ (0.1 : ℝ) ∧ (cell12906 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12906 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12906 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12906

/-! The local source numeric instances at 12906 have no network premises. -/
namespace BstLean.Part269.N12906
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12906)
open BstLean.Part268 (cell12906)

noncomputable def sourceNumerics12906 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12906 (cell12906 i)
      scalarRow12906.M scalarRow12906.H scalarRow12906.xi := by
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
    energy_allowance := scalarRow12906.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12906]
    centre_nonneg := (scalarRow12906.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12906])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12906
/-! Actual 12907 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12907 ≤ (1.035518394211 : ℝ) := by
  have hr : (113.608978518425 : ℝ) ≤ √(12907 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.608978518425 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12907 12907 (11 / 1000) ≤
    (0.008413832979 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12907) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.608978518425 : ℝ) ≤ √(12907 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12907)
  have hdiv : K / √(12907 : ℝ) ≤ K / 113.608978518425 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.608978518425 ≤ (0.008413832979 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12907.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12907 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12907 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12907 := gPlus_lower 12907
end BstLean.Part269.N12907

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12907
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035518394210 : ℝ) ≤ wn 12907 := by
  have hn : √(12907 : ℝ) ≤ 113.608978518426 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12907 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.608978518426 ≤ 2 / √(12907 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247771665 : ℝ) ≤ rhoBar 12907 BstLean.Part154.csC ∧
    rhoBar 12907 BstLean.Part154.csC ≤ 0.000247772048 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035518394210 : ℝ) / (1.295212 * 12907) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035518394211 : ℝ) / (1.29521 * 12907) := by gcongr
      _ ≤ (0.000247772048 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12907 BstLean.Part154.csC) ≤ 0.000991149583 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12907 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) ≤ 0.000189249818 ∧
    cc1 (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) ≤ 0.000120420945 ∧
    cc2 (rhoBar 12907 BstLean.Part154.csC) ≤ 0.000069905317 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12907 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12907 BstLean.Part154.csC * nuR (rhoBar 12907 BstLean.Part154.csC)) ≤ 0.000495559444 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247772048 : ℝ) * 0.000991149583 := by gcongr
      _ ≤ (0.000495559444 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12907 BstLean.Part154.csC) * nuR (rhoBar 12907 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991149583 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12907 BstLean.Part154.csC) * rhoBar 12907 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247772048 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247772048 / 2 + 0.399 * 0.000991149583 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189249818 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495559444 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120420945 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247772048 / 1.414213562 := by gcongr
      _ ≤ (0.000069905317 : ℝ) := by norm_num

end BstLean.Part269.N12907

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12907
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) ≤ 1.54670E-7 := by
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12907 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12907 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189249818 : ℝ) ^ 2 + 0.000120420945 ^ 2 + 3 * 0.000069905317 ^ 2 +
        2 * 0.797885 * 0.000189249818 * 0.000120420945 + 2 * 0.000189249818 * 0.000069905317 +
        4 * 0.797885 * 0.000120420945 * 0.000069905317 := by gcongr
    _ ≤ (1.54670E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12907 BstLean.Part154.csC Θ ≤ 0.002585664992 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12907 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12907 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035518394211 * 1.54670E-7 / (0.000247771665 : ℝ) := by gcongr
    _ ≤ 0.002585664992 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12907 BstLean.Part154.csC Θ ≤ 0.002868130111 + 0.000653356676 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12907 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035518394211 : ℝ) * ((2 * Θ * 0.000247772048 +
        (6863 / 10000) * 0.000247772048 * 12907 * 0.000991149583) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002868130111 + 0.000653356676 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12907 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12907 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12907 0.011 Θ ∧ gammaRatio 12907 0.011 Θ ≤ 0.000085177623 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12907 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035518394211 : ℝ) * 0.525 / ((1 - 0.011) * 12907) := by gcongr
      _ ≤ (0.000085177623 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12907 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12907 0.011 Θ) :=
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
    badAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12907 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12907 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12907 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12907 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12907 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12907 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12907 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12907 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12907 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12907 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035518394211 : ℝ) * 12907 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003331801128 + 0.003239021668 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12907

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12907
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12907 BstLean.Part154.csC) (piBar (rhoBar 12907 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12907 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12907 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12907 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12907 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12907 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12907 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12907 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12907 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12907 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052057199785 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12907) ≤ 0.010511823948 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12907 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035518394211)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010511823948 + 2 * 0.737676 / 12907) := by gcongr
    _ ≤ (0.052057199785 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12907 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12907

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12907
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512779313 : ℝ) ≤ plow 12907 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12907) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538887504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357474121) : eMP 12907 0.011 xi bn ≤ 0.001168935910 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12907 : ℝ) * (1 - 0.011))) ≤ 0.000578002796 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357474121 / (12907 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578002796 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578002796 : ℝ) + 3.141593 * 0.052538887504 / (12907 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168935910 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538887504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357474121) : PiBarMP 12907 12 0.011 xi bn ≤ 0.159939779427 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12907 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036843915658 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.982401284447 : ℝ) ≤ √((12907 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.608978518425 : ℝ) ≤ √(12907 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12907) ≤ 0.122634746342 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036843915658 + 0.052538887504 * 1.772454 / (2 * (112.982401284447 : ℝ))) * (1 + 0.001168935910) +
        8 / (12907 * 113.608978518425) + 0.122634746342 := by gcongr
    _ ≤ (0.159939779427 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538887504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357474121) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281270828316) :
    parallelOracle 12907 0.011 xi bn cd ≤ 0.160914191078 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12907 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12907 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512779313 : ℝ) ≤ plow 12907 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.608978518425 : ℝ) ≤ √(12907 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281270828316 : ℝ) / (2 * 0.560512779313 * 113.608978518425)) * 0.159939779427 +
        0.281270828316 ^ 2 / (2 * 0.560512779313 * 113.608978518425) := by gcongr
    _ ≤ (0.160914191078 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538887504) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357474121)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281270828316) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12907 12907 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512779313 : ℝ) ≤ plow 12907 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.608978518425 : ℝ) ≤ √(12907 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12907 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12907 Θ 1.22 ≤ 0.011672497344 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.608978518425 := by gcongr <;> linarith
      _ ≤ (0.011672497344 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12907 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12907 12907 0.011 ≤ 0.008413832979 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12907 12907 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12907 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12907 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12907 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12907 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160914191078 + 0.011672497344 + (0.008413832979 : ℝ) *
        (1 + 2 * (0.281270828316 + 0.011672497344) / (0.560512779313 * 113.608978518425))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12907]

end BstLean.Part269.N12907

/-! The original eight local profiles supply actual 12907 moment certificates. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12907 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052538887504 ∧
    0 ≤ bN 12907 BstLean.Part154.csC (groupTheta g) ∧ bN 12907 BstLean.Part154.csC (groupTheta g) ≤ 0.001357474121 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12907 12907 0.011
      (momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12907 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12907 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12907 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229213628531 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12907 0.011
      (momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12907 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12907
/-! The actual computed-centre upper energy formula at 12907. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12907

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12907)
open BstLean.Part268 (cell12907)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084908285757
  | 2 => 0.085840817781
  | 3 => 0.086770076916
  | 4 => 0.087697150643
  | 5 => 0.088623364362
  | 6 => 0.089550317992
  | 7 => 0.090479926256
  | 8 => 0.091414462728
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12907 12907 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12907 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12907

/-! Actual upper energy certificates on all 43 source endpoints at 12907. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12907)
open BstLean.Part268 (cell12907)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12907 (gMinus 12907) (1 - (cell12907 i).lower) ≤ 1 ∧
    energyUpper 12907 (gMinus 12907) (BstLean.Part211.gPlus 12907)
      (finiteEnergy 12907 12907 0.011) (1 - (cell12907 i).lower) ≤
      (cell12907 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨10,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨11,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨12,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨13,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨14,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨15,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨16,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨17,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨18,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨19,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨20,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨21,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨22,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨23,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨24,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨25,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨26,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨27,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨28,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨29,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨30,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨31,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨32,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨33,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨34,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨35,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨36,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨37,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨38,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨39,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨40,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨41,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨42,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨43,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨44,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨45,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨46,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨47,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨48,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨49,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨50,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨51,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12907) (by norm_num)
        (q := 1 - (cell12907 ⟨52,by decide⟩).lower)
        (by norm_num [cell12907]) (by norm_num [cell12907])
      exact ⟨E.1,E.2.trans (by norm_num [cell12907])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12907

/-! Source-cell containment and simple scalar guards at 12907. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12907)
open BstLean.Part268 (cell12907)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12907 ⟨10,by decide⟩).lower ∧ (cell12907 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12907 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12907 ⟨11,by decide⟩).lower ∧ (cell12907 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12907 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12907 ⟨12,by decide⟩).lower ∧ (cell12907 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12907 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12907 ⟨13,by decide⟩).lower ∧ (cell12907 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12907 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12907 ⟨14,by decide⟩).lower ∧ (cell12907 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12907 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12907 ⟨15,by decide⟩).lower ∧ (cell12907 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12907 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12907 ⟨16,by decide⟩).lower ∧ (cell12907 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12907 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12907 ⟨17,by decide⟩).lower ∧ (cell12907 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12907 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12907 ⟨18,by decide⟩).lower ∧ (cell12907 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12907 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12907 ⟨19,by decide⟩).lower ∧ (cell12907 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12907 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12907 ⟨20,by decide⟩).lower ∧ (cell12907 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12907 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12907 ⟨21,by decide⟩).lower ∧ (cell12907 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12907 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12907 ⟨22,by decide⟩).lower ∧ (cell12907 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12907 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12907 ⟨23,by decide⟩).lower ∧ (cell12907 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12907 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12907 ⟨24,by decide⟩).lower ∧ (cell12907 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12907 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12907 ⟨25,by decide⟩).lower ∧ (cell12907 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12907 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12907 ⟨26,by decide⟩).lower ∧ (cell12907 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12907 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12907 ⟨27,by decide⟩).lower ∧ (cell12907 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12907 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12907 ⟨28,by decide⟩).lower ∧ (cell12907 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12907 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12907 ⟨29,by decide⟩).lower ∧ (cell12907 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12907 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12907 ⟨30,by decide⟩).lower ∧ (cell12907 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12907 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12907 ⟨31,by decide⟩).lower ∧ (cell12907 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12907 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12907 ⟨32,by decide⟩).lower ∧ (cell12907 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12907 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12907 ⟨33,by decide⟩).lower ∧ (cell12907 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12907 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12907 ⟨34,by decide⟩).lower ∧ (cell12907 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12907 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12907 ⟨35,by decide⟩).lower ∧ (cell12907 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12907 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12907 ⟨36,by decide⟩).lower ∧ (cell12907 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12907 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12907 ⟨37,by decide⟩).lower ∧ (cell12907 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12907 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12907 ⟨38,by decide⟩).lower ∧ (cell12907 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12907 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12907 ⟨39,by decide⟩).lower ∧ (cell12907 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12907 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12907 ⟨40,by decide⟩).lower ∧ (cell12907 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12907 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12907 ⟨41,by decide⟩).lower ∧ (cell12907 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12907 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12907 ⟨42,by decide⟩).lower ∧ (cell12907 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12907 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12907 ⟨43,by decide⟩).lower ∧ (cell12907 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12907 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12907 ⟨44,by decide⟩).lower ∧ (cell12907 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12907 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12907 ⟨45,by decide⟩).lower ∧ (cell12907 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12907 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12907 ⟨46,by decide⟩).lower ∧ (cell12907 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12907 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12907 ⟨47,by decide⟩).lower ∧ (cell12907 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12907 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12907 ⟨48,by decide⟩).lower ∧ (cell12907 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12907 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12907 ⟨49,by decide⟩).lower ∧ (cell12907 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12907 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12907 ⟨50,by decide⟩).lower ∧ (cell12907 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12907 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12907 ⟨51,by decide⟩).lower ∧ (cell12907 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12907 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12907 ⟨52,by decide⟩).lower ∧ (cell12907 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12907 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12907 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12907 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12907,cell12907,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12907 i).lower ∧
    (cell12907 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12907 i).upper ≤ (0.532 : ℝ) ∧
    (cell12907 i).centre ≤ (0.1 : ℝ) ∧ (cell12907 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12907 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12907 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12907

/-! The local source numeric instances at 12907 have no network premises. -/
namespace BstLean.Part269.N12907
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12907)
open BstLean.Part268 (cell12907)

noncomputable def sourceNumerics12907 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12907 (cell12907 i)
      scalarRow12907.M scalarRow12907.H scalarRow12907.xi := by
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
    energy_allowance := scalarRow12907.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12907]
    centre_nonneg := (scalarRow12907.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12907])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12907
/-! Actual 12908 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12908 ≤ (1.035517006351 : ℝ) := by
  have hr : (113.613379493790 : ℝ) ≤ √(12908 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.613379493790 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12908 12908 (11 / 1000) ≤
    (0.008413507055 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12908) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.613379493790 : ℝ) ≤ √(12908 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12908)
  have hdiv : K / √(12908 : ℝ) ≤ K / 113.613379493790 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.613379493790 ≤ (0.008413507055 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12908.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12908 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12908 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12908 := gPlus_lower 12908
end BstLean.Part269.N12908

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12908
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035517006350 : ℝ) ≤ wn 12908 := by
  have hn : √(12908 : ℝ) ≤ 113.613379493791 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12908 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.613379493791 ≤ 2 / √(12908 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247752137 : ℝ) ≤ rhoBar 12908 BstLean.Part154.csC ∧
    rhoBar 12908 BstLean.Part154.csC ≤ 0.000247752521 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035517006350 : ℝ) / (1.295212 * 12908) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035517006351 : ℝ) / (1.29521 * 12908) := by gcongr
      _ ≤ (0.000247752521 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12908 BstLean.Part154.csC) ≤ 0.000991071466 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12908 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) ≤ 0.000189234903 ∧
    cc1 (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) ≤ 0.000120411455 ∧
    cc2 (rhoBar 12908 BstLean.Part154.csC) ≤ 0.000069899808 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12908 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12908 BstLean.Part154.csC * nuR (rhoBar 12908 BstLean.Part154.csC)) ≤ 0.000495520388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247752521 : ℝ) * 0.000991071466 := by gcongr
      _ ≤ (0.000495520388 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12908 BstLean.Part154.csC) * nuR (rhoBar 12908 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991071466 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12908 BstLean.Part154.csC) * rhoBar 12908 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247752521 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247752521 / 2 + 0.399 * 0.000991071466 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189234903 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495520388 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120411455 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247752521 / 1.414213562 := by gcongr
      _ ≤ (0.000069899808 : ℝ) := by norm_num

end BstLean.Part269.N12908

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12908
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) ≤ 1.54646E-7 := by
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12908 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12908 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189234903 : ℝ) ^ 2 + 0.000120411455 ^ 2 + 3 * 0.000069899808 ^ 2 +
        2 * 0.797885 * 0.000189234903 * 0.000120411455 + 2 * 0.000189234903 * 0.000069899808 +
        4 * 0.797885 * 0.000120411455 * 0.000069899808 := by gcongr
    _ ≤ (1.54646E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12908 BstLean.Part154.csC Θ ≤ 0.002585464084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12908 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12908 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035517006351 * 1.54646E-7 / (0.000247752137 : ℝ) := by gcongr
    _ ≤ 0.002585464084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12908 BstLean.Part154.csC Θ ≤ 0.002867896377 + 0.000653304310 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12908 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035517006351 : ℝ) * ((2 * Θ * 0.000247752521 +
        (6863 / 10000) * 0.000247752521 * 12908 * 0.000991071466) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002867896377 + 0.000653304310 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12908 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12908 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12908 0.011 Θ ∧ gammaRatio 12908 0.011 Θ ≤ 0.000085170910 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12908 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035517006351 : ℝ) * 0.525 / ((1 - 0.011) * 12908) := by gcongr
      _ ≤ (0.000085170910 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12908 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12908 0.011 Θ) :=
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
    badAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12908 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12908 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12908 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12908 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12908 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12908 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12908 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12908 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12908 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12908 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035517006351 : ℝ) * 12908 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003331567394 + 0.003238768394 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12908

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12908
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12908 BstLean.Part154.csC) (piBar (rhoBar 12908 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12908 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12908 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12908 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12908 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12908 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12908 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12908 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12908 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12908 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052055161587 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12908) ≤ 0.010511416758 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12908 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035517006351)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010511416758 + 2 * 0.737676 / 12908) := by gcongr
    _ ≤ (0.052055161587 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12908 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12908

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12908
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512823094 : ℝ) ≤ plow 12908 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12908) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538520801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357368645) : eMP 12908 0.011 xi bn ≤ 0.001168845128 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12908 : ℝ) * (1 - 0.011))) ≤ 0.000577957951 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357368645 / (12908 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577957951 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577957951 : ℝ) + 3.141593 * 0.052538520801 / (12908 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168845128 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538520801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357368645) : PiBarMP 12908 12 0.011 xi bn ≤ 0.159933573028 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12908 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036842484241 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.986777987514 : ℝ) ≤ √((12908 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.613379493790 : ℝ) ≤ √(12908 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12908) ≤ 0.122629995911 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036842484241 + 0.052538520801 * 1.772454 / (2 * (112.986777987514 : ℝ))) * (1 + 0.001168845128) +
        8 / (12908 * 113.613379493790) + 0.122629995911 := by gcongr
    _ ≤ (0.159933573028 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538520801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357368645) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281267990201) :
    parallelOracle 12908 0.011 xi bn cd ≤ 0.160907917053 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12908 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12908 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512823094 : ℝ) ≤ plow 12908 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.613379493790 : ℝ) ≤ √(12908 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281267990201 : ℝ) / (2 * 0.560512823094 * 113.613379493790)) * 0.159933573028 +
        0.281267990201 ^ 2 / (2 * 0.560512823094 * 113.613379493790) := by gcongr
    _ ≤ (0.160907917053 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538520801) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357368645)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281267990201) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12908 12908 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512823094 : ℝ) ≤ plow 12908 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.613379493790 : ℝ) ≤ √(12908 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12908 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12908 Θ 1.22 ≤ 0.011672045194 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.613379493790 := by gcongr <;> linarith
      _ ≤ (0.011672045194 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12908 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12908 12908 0.011 ≤ 0.008413507055 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12908 12908 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12908 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12908 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12908 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12908 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160907917053 + 0.011672045194 + (0.008413507055 : ℝ) *
        (1 + 2 * (0.281267990201 + 0.011672045194) / (0.560512823094 * 113.613379493790))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12908]

end BstLean.Part269.N12908

/-! The original eight local profiles supply actual 12908 moment certificates. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12908 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052538520801 ∧
    0 ≤ bN 12908 BstLean.Part154.csC (groupTheta g) ∧ bN 12908 BstLean.Part154.csC (groupTheta g) ≤ 0.001357368645 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12908 12908 0.011
      (momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12908 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12908 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12908 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229212828614 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12908 0.011
      (momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12908 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12908
/-! The actual computed-centre upper energy formula at 12908. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12908

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12908)
open BstLean.Part268 (cell12908)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084905572715
  | 2 => 0.085838059259
  | 3 => 0.086767267001
  | 4 => 0.087694282016
  | 5 => 0.088620428039
  | 6 => 0.089547303035
  | 7 => 0.090476819445
  | 8 => 0.091411248203
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12908 12908 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12908 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12908

/-! Actual upper energy certificates on all 43 source endpoints at 12908. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12908)
open BstLean.Part268 (cell12908)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12908 (gMinus 12908) (1 - (cell12908 i).lower) ≤ 1 ∧
    energyUpper 12908 (gMinus 12908) (BstLean.Part211.gPlus 12908)
      (finiteEnergy 12908 12908 0.011) (1 - (cell12908 i).lower) ≤
      (cell12908 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨10,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨11,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨12,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨13,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨14,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨15,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨16,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨17,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨18,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨19,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨20,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨21,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨22,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨23,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨24,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨25,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨26,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨27,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨28,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨29,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨30,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨31,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨32,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨33,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨34,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨35,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨36,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨37,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨38,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨39,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨40,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨41,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨42,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨43,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨44,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨45,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨46,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨47,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨48,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨49,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨50,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨51,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12908) (by norm_num)
        (q := 1 - (cell12908 ⟨52,by decide⟩).lower)
        (by norm_num [cell12908]) (by norm_num [cell12908])
      exact ⟨E.1,E.2.trans (by norm_num [cell12908])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12908

/-! Source-cell containment and simple scalar guards at 12908. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12908)
open BstLean.Part268 (cell12908)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12908 ⟨10,by decide⟩).lower ∧ (cell12908 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12908 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12908 ⟨11,by decide⟩).lower ∧ (cell12908 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12908 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12908 ⟨12,by decide⟩).lower ∧ (cell12908 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12908 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12908 ⟨13,by decide⟩).lower ∧ (cell12908 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12908 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12908 ⟨14,by decide⟩).lower ∧ (cell12908 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12908 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12908 ⟨15,by decide⟩).lower ∧ (cell12908 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12908 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12908 ⟨16,by decide⟩).lower ∧ (cell12908 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12908 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12908 ⟨17,by decide⟩).lower ∧ (cell12908 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12908 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12908 ⟨18,by decide⟩).lower ∧ (cell12908 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12908 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12908 ⟨19,by decide⟩).lower ∧ (cell12908 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12908 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12908 ⟨20,by decide⟩).lower ∧ (cell12908 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12908 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12908 ⟨21,by decide⟩).lower ∧ (cell12908 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12908 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12908 ⟨22,by decide⟩).lower ∧ (cell12908 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12908 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12908 ⟨23,by decide⟩).lower ∧ (cell12908 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12908 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12908 ⟨24,by decide⟩).lower ∧ (cell12908 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12908 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12908 ⟨25,by decide⟩).lower ∧ (cell12908 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12908 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12908 ⟨26,by decide⟩).lower ∧ (cell12908 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12908 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12908 ⟨27,by decide⟩).lower ∧ (cell12908 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12908 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12908 ⟨28,by decide⟩).lower ∧ (cell12908 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12908 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12908 ⟨29,by decide⟩).lower ∧ (cell12908 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12908 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12908 ⟨30,by decide⟩).lower ∧ (cell12908 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12908 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12908 ⟨31,by decide⟩).lower ∧ (cell12908 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12908 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12908 ⟨32,by decide⟩).lower ∧ (cell12908 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12908 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12908 ⟨33,by decide⟩).lower ∧ (cell12908 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12908 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12908 ⟨34,by decide⟩).lower ∧ (cell12908 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12908 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12908 ⟨35,by decide⟩).lower ∧ (cell12908 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12908 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12908 ⟨36,by decide⟩).lower ∧ (cell12908 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12908 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12908 ⟨37,by decide⟩).lower ∧ (cell12908 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12908 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12908 ⟨38,by decide⟩).lower ∧ (cell12908 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12908 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12908 ⟨39,by decide⟩).lower ∧ (cell12908 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12908 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12908 ⟨40,by decide⟩).lower ∧ (cell12908 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12908 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12908 ⟨41,by decide⟩).lower ∧ (cell12908 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12908 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12908 ⟨42,by decide⟩).lower ∧ (cell12908 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12908 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12908 ⟨43,by decide⟩).lower ∧ (cell12908 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12908 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12908 ⟨44,by decide⟩).lower ∧ (cell12908 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12908 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12908 ⟨45,by decide⟩).lower ∧ (cell12908 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12908 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12908 ⟨46,by decide⟩).lower ∧ (cell12908 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12908 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12908 ⟨47,by decide⟩).lower ∧ (cell12908 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12908 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12908 ⟨48,by decide⟩).lower ∧ (cell12908 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12908 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12908 ⟨49,by decide⟩).lower ∧ (cell12908 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12908 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12908 ⟨50,by decide⟩).lower ∧ (cell12908 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12908 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12908 ⟨51,by decide⟩).lower ∧ (cell12908 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12908 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12908 ⟨52,by decide⟩).lower ∧ (cell12908 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12908 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12908 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12908 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12908,cell12908,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12908 i).lower ∧
    (cell12908 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12908 i).upper ≤ (0.532 : ℝ) ∧
    (cell12908 i).centre ≤ (0.1 : ℝ) ∧ (cell12908 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12908 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12908 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12908

/-! The local source numeric instances at 12908 have no network premises. -/
namespace BstLean.Part269.N12908
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12908)
open BstLean.Part268 (cell12908)

noncomputable def sourceNumerics12908 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12908 (cell12908 i)
      scalarRow12908.M scalarRow12908.H scalarRow12908.xi := by
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
    energy_allowance := scalarRow12908.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12908]
    centre_nonneg := (scalarRow12908.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12908])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12908
/-! Actual 12909 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12909 ≤ (1.035515618654 : ℝ) := by
  have hr : (113.617780298683 : ℝ) ≤ √(12909 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.617780298683 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12909 12909 (11 / 1000) ≤
    (0.008413181169 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12909) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.617780298683 : ℝ) ≤ √(12909 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12909)
  have hdiv : K / √(12909 : ℝ) ≤ K / 113.617780298683 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.617780298683 ≤ (0.008413181169 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12909.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12909 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12909 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12909 := gPlus_lower 12909
end BstLean.Part269.N12909

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12909
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035515618653 : ℝ) ≤ wn 12909 := by
  have hn : √(12909 : ℝ) ≤ 113.617780298684 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12909 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.617780298684 ≤ 2 / √(12909 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247732613 : ℝ) ≤ rhoBar 12909 BstLean.Part154.csC ∧
    rhoBar 12909 BstLean.Part154.csC ≤ 0.000247732997 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035515618653 : ℝ) / (1.295212 * 12909) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035515618654 : ℝ) / (1.29521 * 12909) := by gcongr
      _ ≤ (0.000247732997 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12909 BstLean.Part154.csC) ≤ 0.000990993360 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12909 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) ≤ 0.000189219989 ∧
    cc1 (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) ≤ 0.000120401965 ∧
    cc2 (rhoBar 12909 BstLean.Part154.csC) ≤ 0.000069894300 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12909 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12909 BstLean.Part154.csC * nuR (rhoBar 12909 BstLean.Part154.csC)) ≤ 0.000495481337 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247732997 : ℝ) * 0.000990993360 := by gcongr
      _ ≤ (0.000495481337 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12909 BstLean.Part154.csC) * nuR (rhoBar 12909 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990993360 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12909 BstLean.Part154.csC) * rhoBar 12909 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247732997 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247732997 / 2 + 0.399 * 0.000990993360 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189219989 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495481337 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120401965 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247732997 / 1.414213562 := by gcongr
      _ ≤ (0.000069894300 : ℝ) := by norm_num

end BstLean.Part269.N12909

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12909
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) ≤ 1.54621E-7 := by
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12909 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12909 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189219989 : ℝ) ^ 2 + 0.000120401965 ^ 2 + 3 * 0.000069894300 ^ 2 +
        2 * 0.797885 * 0.000189219989 * 0.000120401965 + 2 * 0.000189219989 * 0.000069894300 +
        4 * 0.797885 * 0.000120401965 * 0.000069894300 := by gcongr
    _ ≤ (1.54621E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12909 BstLean.Part154.csC Θ ≤ 0.002585246384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12909 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12909 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035515618654 * 1.54621E-7 / (0.000247732613 : ℝ) := by gcongr
    _ ≤ 0.002585246384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12909 BstLean.Part154.csC Θ ≤ 0.002867662675 + 0.000653251951 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12909 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035515618654 : ℝ) * ((2 * Θ * 0.000247732997 +
        (6863 / 10000) * 0.000247732997 * 12909 * 0.000990993360) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002867662675 + 0.000653251951 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12909 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12909 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12909 0.011 Θ ∧ gammaRatio 12909 0.011 Θ ≤ 0.000085164198 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12909 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035515618654 : ℝ) * 0.525 / ((1 - 0.011) * 12909) := by gcongr
      _ ≤ (0.000085164198 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12909 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12909 0.011 Θ) :=
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
    badAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12909 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12909 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12909 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12909 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12909 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12909 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12909 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12909 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12909 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12909 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035515618654 : ℝ) * 12909 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003331333692 + 0.003238498335 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12909

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12909
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12909 BstLean.Part154.csC) (piBar (rhoBar 12909 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12909 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12909 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12909 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12909 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12909 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12909 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12909 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12909 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12909 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052053123625 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12909) ≤ 0.010511009615 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12909 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035515618654)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010511009615 + 2 * 0.737676 / 12909) := by gcongr
    _ ≤ (0.052053123625 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12909 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12909

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12909
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512866868 : ℝ) ≤ plow 12909 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12909) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538145318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357254352) : eMP 12909 0.011 xi bn ≤ 0.001168750598 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12909 : ℝ) * (1 - 0.011))) ≤ 0.000577911233 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357254352 / (12909 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577911233 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577911233 : ℝ) + 3.141593 * 0.052538145318 / (12909 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168750598 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538145318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357254352) : PiBarMP 12909 12 0.011 xi bn ≤ 0.159927247117 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12909 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036840933105 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.991154521050 : ℝ) ≤ √((12909 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.617780298683 : ℝ) ≤ √(12909 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12909) ≤ 0.122625246033 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036840933105 + 0.052538145318 * 1.772454 / (2 * (112.991154521050 : ℝ))) * (1 + 0.001168750598) +
        8 / (12909 * 113.617780298683) + 0.122625246033 := by gcongr
    _ ≤ (0.159927247117 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538145318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357254352) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281265133167) :
    parallelOracle 12909 0.011 xi bn cd ≤ 0.160901523151 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12909 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12909 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512866868 : ℝ) ≤ plow 12909 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.617780298683 : ℝ) ≤ √(12909 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281265133167 : ℝ) / (2 * 0.560512866868 * 113.617780298683)) * 0.159927247117 +
        0.281265133167 ^ 2 / (2 * 0.560512866868 * 113.617780298683) := by gcongr
    _ ≤ (0.160901523151 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052538145318) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357254352)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281265133167) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12909 12909 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512866868 : ℝ) ≤ plow 12909 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.617780298683 : ℝ) ≤ √(12909 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12909 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12909 Θ 1.22 ≤ 0.011671593095 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.617780298683 := by gcongr <;> linarith
      _ ≤ (0.011671593095 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12909 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12909 12909 0.011 ≤ 0.008413181169 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12909 12909 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12909 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12909 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12909 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12909 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160901523151 + 0.011671593095 + (0.008413181169 : ℝ) *
        (1 + 2 * (0.281265133167 + 0.011671593095) / (0.560512866868 * 113.617780298683))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12909]

end BstLean.Part269.N12909

/-! The original eight local profiles supply actual 12909 moment certificates. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12909 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052538145318 ∧
    0 ≤ bN 12909 BstLean.Part154.csC (groupTheta g) ∧ bN 12909 BstLean.Part154.csC (groupTheta g) ≤ 0.001357254352 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12909 12909 0.011
      (momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12909 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12909 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12909 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229212009542 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12909 0.011
      (momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12909 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12909
/-! The actual computed-centre upper energy formula at 12909. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12909

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12909)
open BstLean.Part268 (cell12909)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084902860557
  | 2 => 0.085835301653
  | 3 => 0.086764458046
  | 4 => 0.087691414401
  | 5 => 0.088617492792
  | 6 => 0.089544289230
  | 7 => 0.090473713881
  | 8 => 0.091408035036
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12909 12909 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12909 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12909

/-! Actual upper energy certificates on all 43 source endpoints at 12909. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12909)
open BstLean.Part268 (cell12909)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12909 (gMinus 12909) (1 - (cell12909 i).lower) ≤ 1 ∧
    energyUpper 12909 (gMinus 12909) (BstLean.Part211.gPlus 12909)
      (finiteEnergy 12909 12909 0.011) (1 - (cell12909 i).lower) ≤
      (cell12909 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨10,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨11,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨12,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨13,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨14,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨15,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨16,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨17,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨18,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨19,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨20,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨21,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨22,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨23,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨24,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨25,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨26,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨27,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨28,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨29,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨30,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨31,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨32,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨33,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨34,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨35,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨36,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨37,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨38,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨39,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨40,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨41,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨42,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨43,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨44,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨45,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨46,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨47,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨48,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨49,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨50,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨51,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12909) (by norm_num)
        (q := 1 - (cell12909 ⟨52,by decide⟩).lower)
        (by norm_num [cell12909]) (by norm_num [cell12909])
      exact ⟨E.1,E.2.trans (by norm_num [cell12909])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12909

/-! Source-cell containment and simple scalar guards at 12909. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12909)
open BstLean.Part268 (cell12909)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12909 ⟨10,by decide⟩).lower ∧ (cell12909 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12909 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12909 ⟨11,by decide⟩).lower ∧ (cell12909 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12909 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12909 ⟨12,by decide⟩).lower ∧ (cell12909 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12909 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12909 ⟨13,by decide⟩).lower ∧ (cell12909 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12909 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12909 ⟨14,by decide⟩).lower ∧ (cell12909 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12909 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12909 ⟨15,by decide⟩).lower ∧ (cell12909 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12909 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12909 ⟨16,by decide⟩).lower ∧ (cell12909 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12909 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12909 ⟨17,by decide⟩).lower ∧ (cell12909 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12909 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12909 ⟨18,by decide⟩).lower ∧ (cell12909 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12909 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12909 ⟨19,by decide⟩).lower ∧ (cell12909 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12909 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12909 ⟨20,by decide⟩).lower ∧ (cell12909 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12909 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12909 ⟨21,by decide⟩).lower ∧ (cell12909 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12909 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12909 ⟨22,by decide⟩).lower ∧ (cell12909 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12909 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12909 ⟨23,by decide⟩).lower ∧ (cell12909 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12909 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12909 ⟨24,by decide⟩).lower ∧ (cell12909 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12909 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12909 ⟨25,by decide⟩).lower ∧ (cell12909 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12909 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12909 ⟨26,by decide⟩).lower ∧ (cell12909 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12909 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12909 ⟨27,by decide⟩).lower ∧ (cell12909 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12909 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12909 ⟨28,by decide⟩).lower ∧ (cell12909 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12909 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12909 ⟨29,by decide⟩).lower ∧ (cell12909 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12909 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12909 ⟨30,by decide⟩).lower ∧ (cell12909 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12909 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12909 ⟨31,by decide⟩).lower ∧ (cell12909 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12909 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12909 ⟨32,by decide⟩).lower ∧ (cell12909 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12909 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12909 ⟨33,by decide⟩).lower ∧ (cell12909 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12909 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12909 ⟨34,by decide⟩).lower ∧ (cell12909 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12909 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12909 ⟨35,by decide⟩).lower ∧ (cell12909 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12909 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12909 ⟨36,by decide⟩).lower ∧ (cell12909 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12909 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12909 ⟨37,by decide⟩).lower ∧ (cell12909 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12909 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12909 ⟨38,by decide⟩).lower ∧ (cell12909 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12909 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12909 ⟨39,by decide⟩).lower ∧ (cell12909 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12909 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12909 ⟨40,by decide⟩).lower ∧ (cell12909 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12909 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12909 ⟨41,by decide⟩).lower ∧ (cell12909 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12909 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12909 ⟨42,by decide⟩).lower ∧ (cell12909 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12909 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12909 ⟨43,by decide⟩).lower ∧ (cell12909 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12909 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12909 ⟨44,by decide⟩).lower ∧ (cell12909 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12909 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12909 ⟨45,by decide⟩).lower ∧ (cell12909 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12909 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12909 ⟨46,by decide⟩).lower ∧ (cell12909 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12909 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12909 ⟨47,by decide⟩).lower ∧ (cell12909 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12909 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12909 ⟨48,by decide⟩).lower ∧ (cell12909 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12909 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12909 ⟨49,by decide⟩).lower ∧ (cell12909 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12909 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12909 ⟨50,by decide⟩).lower ∧ (cell12909 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12909 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12909 ⟨51,by decide⟩).lower ∧ (cell12909 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12909 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12909 ⟨52,by decide⟩).lower ∧ (cell12909 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12909 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12909 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12909 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12909,cell12909,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12909 i).lower ∧
    (cell12909 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12909 i).upper ≤ (0.532 : ℝ) ∧
    (cell12909 i).centre ≤ (0.1 : ℝ) ∧ (cell12909 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12909 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12909 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12909

/-! The local source numeric instances at 12909 have no network premises. -/
namespace BstLean.Part269.N12909
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12909)
open BstLean.Part268 (cell12909)

noncomputable def sourceNumerics12909 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12909 (cell12909 i)
      scalarRow12909.M scalarRow12909.H scalarRow12909.xi := by
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
    energy_allowance := scalarRow12909.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12909]
    centre_nonneg := (scalarRow12909.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12909])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12909
/-! Actual 12910 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12910 ≤ (1.035514231118 : ℝ) := by
  have hr : (113.622180933125 : ℝ) ≤ √(12910 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.622180933125 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12910 12910 (11 / 1000) ≤
    (0.008412855320 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12910) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.622180933125 : ℝ) ≤ √(12910 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12910)
  have hdiv : K / √(12910 : ℝ) ≤ K / 113.622180933125 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.622180933125 ≤ (0.008412855320 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12910.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12910 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12910 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12910 := gPlus_lower 12910
end BstLean.Part269.N12910

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12910
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035514231117 : ℝ) ≤ wn 12910 := by
  have hn : √(12910 : ℝ) ≤ 113.622180933126 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12910 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.622180933126 ≤ 2 / √(12910 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247713092 : ℝ) ≤ rhoBar 12910 BstLean.Part154.csC ∧
    rhoBar 12910 BstLean.Part154.csC ≤ 0.000247713476 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035514231117 : ℝ) / (1.295212 * 12910) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035514231118 : ℝ) / (1.29521 * 12910) := by gcongr
      _ ≤ (0.000247713476 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12910 BstLean.Part154.csC) ≤ 0.000990915266 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12910 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) ≤ 0.000189205078 ∧
    cc1 (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) ≤ 0.000120392478 ∧
    cc2 (rhoBar 12910 BstLean.Part154.csC) ≤ 0.000069888792 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12910 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12910 BstLean.Part154.csC * nuR (rhoBar 12910 BstLean.Part154.csC)) ≤ 0.000495442293 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247713476 : ℝ) * 0.000990915266 := by gcongr
      _ ≤ (0.000495442293 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12910 BstLean.Part154.csC) * nuR (rhoBar 12910 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990915266 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12910 BstLean.Part154.csC) * rhoBar 12910 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247713476 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247713476 / 2 + 0.399 * 0.000990915266 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189205078 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495442293 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120392478 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247713476 / 1.414213562 := by gcongr
      _ ≤ (0.000069888792 : ℝ) := by norm_num

end BstLean.Part269.N12910

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12910
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) ≤ 1.54597E-7 := by
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12910 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12910 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189205078 : ℝ) ^ 2 + 0.000120392478 ^ 2 + 3 * 0.000069888792 ^ 2 +
        2 * 0.797885 * 0.000189205078 * 0.000120392478 + 2 * 0.000189205078 * 0.000069888792 +
        4 * 0.797885 * 0.000120392478 * 0.000069888792 := by gcongr
    _ ≤ (1.54597E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12910 BstLean.Part154.csC Θ ≤ 0.002585045341 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12910 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12910 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035514231118 * 1.54597E-7 / (0.000247713092 : ℝ) := by gcongr
    _ ≤ 0.002585045341 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12910 BstLean.Part154.csC Θ ≤ 0.002867429010 + 0.000653199600 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12910 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035514231118 : ℝ) * ((2 * Θ * 0.000247713476 +
        (6863 / 10000) * 0.000247713476 * 12910 * 0.000990915266) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002867429010 + 0.000653199600 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12910 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12910 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12910 0.011 Θ ∧ gammaRatio 12910 0.011 Θ ≤ 0.000085157488 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12910 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035514231118 : ℝ) * 0.525 / ((1 - 0.011) * 12910) := by gcongr
      _ ≤ (0.000085157488 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12910 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12910 0.011 Θ) :=
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
    badAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12910 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12910 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12910 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12910 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12910 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12910 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12910 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12910 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12910 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12910 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035514231118 : ℝ) * 12910 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003331100027 + 0.003238244941 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12910

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12910
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12910 BstLean.Part154.csC) (piBar (rhoBar 12910 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12910 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12910 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12910 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12910 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12910 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12910 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12910 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12910 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12910 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052051085901 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12910) ≤ 0.010510602519 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12910 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035514231118)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010510602519 + 2 * 0.737676 / 12910) := by gcongr
    _ ≤ (0.052051085901 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12910 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12910

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12910
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512910635 : ℝ) ≤ plow 12910 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12910) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537778622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357148805) : eMP 12910 0.011 xi bn ≤ 0.001168659801 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12910 : ℝ) * (1 - 0.011))) ≤ 0.000577866380 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357148805 / (12910 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577866380 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577866380 : ℝ) + 3.141593 * 0.052537778622 / (12910 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168659801 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537778622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357148805) : PiBarMP 12910 12 0.011 xi bn ≤ 0.159921040745 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12910 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036839500608 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.995530885075 : ℝ) ≤ √((12910 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.622180933125 : ℝ) ≤ √(12910 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12910) ≤ 0.122620496706 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036839500608 + 0.052537778622 * 1.772454 / (2 * (112.995530885075 : ℝ))) * (1 + 0.001168659801) +
        8 / (12910 * 113.622180933125) + 0.122620496706 := by gcongr
    _ ≤ (0.159921040745 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537778622)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357148805) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281262295536) :
    parallelOracle 12910 0.011 xi bn cd ≤ 0.160895249169 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12910 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12910 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512910635 : ℝ) ≤ plow 12910 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.622180933125 : ℝ) ≤ √(12910 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281262295536 : ℝ) / (2 * 0.560512910635 * 113.622180933125)) * 0.159921040745 +
        0.281262295536 ^ 2 / (2 * 0.560512910635 * 113.622180933125) := by gcongr
    _ ≤ (0.160895249169 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537778622) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357148805)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281262295536) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12910 12910 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512910635 : ℝ) ≤ plow 12910 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.622180933125 : ℝ) ≤ √(12910 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12910 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12910 Θ 1.22 ≤ 0.011671141050 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.622180933125 := by gcongr <;> linarith
      _ ≤ (0.011671141050 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12910 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12910 12910 0.011 ≤ 0.008412855320 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12910 12910 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12910 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12910 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12910 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12910 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160895249169 + 0.011671141050 + (0.008412855320 : ℝ) *
        (1 + 2 * (0.281262295536 + 0.011671141050) / (0.560512910635 * 113.622180933125))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12910]

end BstLean.Part269.N12910

/-! The original eight local profiles supply actual 12910 moment certificates. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12910 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052537778622 ∧
    0 ≤ bN 12910 BstLean.Part154.csC (groupTheta g) ∧ bN 12910 BstLean.Part154.csC (groupTheta g) ≤ 0.001357148805 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12910 12910 0.011
      (momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12910 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12910 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12910 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229211209635 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12910 0.011
      (momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12910 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12910
/-! The actual computed-centre upper energy formula at 12910. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12910

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12910)
open BstLean.Part268 (cell12910)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084900149281
  | 2 => 0.085832544965
  | 3 => 0.086761650049
  | 4 => 0.087688547796
  | 5 => 0.088614558617
  | 6 => 0.089541276576
  | 7 => 0.090470609560
  | 8 => 0.091404823226
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12910 12910 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12910 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12910

/-! Actual upper energy certificates on all 43 source endpoints at 12910. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12910)
open BstLean.Part268 (cell12910)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12910 (gMinus 12910) (1 - (cell12910 i).lower) ≤ 1 ∧
    energyUpper 12910 (gMinus 12910) (BstLean.Part211.gPlus 12910)
      (finiteEnergy 12910 12910 0.011) (1 - (cell12910 i).lower) ≤
      (cell12910 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨10,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨11,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨12,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨13,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨14,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨15,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨16,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨17,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨18,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨19,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨20,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨21,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨22,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨23,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨24,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨25,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨26,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨27,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨28,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨29,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨30,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨31,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨32,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨33,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨34,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨35,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨36,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨37,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨38,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨39,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨40,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨41,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨42,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨43,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨44,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨45,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨46,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨47,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨48,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨49,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨50,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨51,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12910) (by norm_num)
        (q := 1 - (cell12910 ⟨52,by decide⟩).lower)
        (by norm_num [cell12910]) (by norm_num [cell12910])
      exact ⟨E.1,E.2.trans (by norm_num [cell12910])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12910

/-! Source-cell containment and simple scalar guards at 12910. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12910)
open BstLean.Part268 (cell12910)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12910 ⟨10,by decide⟩).lower ∧ (cell12910 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12910 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12910 ⟨11,by decide⟩).lower ∧ (cell12910 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12910 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12910 ⟨12,by decide⟩).lower ∧ (cell12910 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12910 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12910 ⟨13,by decide⟩).lower ∧ (cell12910 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12910 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12910 ⟨14,by decide⟩).lower ∧ (cell12910 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12910 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12910 ⟨15,by decide⟩).lower ∧ (cell12910 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12910 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12910 ⟨16,by decide⟩).lower ∧ (cell12910 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12910 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12910 ⟨17,by decide⟩).lower ∧ (cell12910 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12910 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12910 ⟨18,by decide⟩).lower ∧ (cell12910 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12910 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12910 ⟨19,by decide⟩).lower ∧ (cell12910 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12910 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12910 ⟨20,by decide⟩).lower ∧ (cell12910 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12910 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12910 ⟨21,by decide⟩).lower ∧ (cell12910 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12910 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12910 ⟨22,by decide⟩).lower ∧ (cell12910 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12910 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12910 ⟨23,by decide⟩).lower ∧ (cell12910 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12910 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12910 ⟨24,by decide⟩).lower ∧ (cell12910 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12910 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12910 ⟨25,by decide⟩).lower ∧ (cell12910 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12910 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12910 ⟨26,by decide⟩).lower ∧ (cell12910 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12910 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12910 ⟨27,by decide⟩).lower ∧ (cell12910 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12910 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12910 ⟨28,by decide⟩).lower ∧ (cell12910 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12910 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12910 ⟨29,by decide⟩).lower ∧ (cell12910 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12910 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12910 ⟨30,by decide⟩).lower ∧ (cell12910 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12910 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12910 ⟨31,by decide⟩).lower ∧ (cell12910 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12910 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12910 ⟨32,by decide⟩).lower ∧ (cell12910 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12910 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12910 ⟨33,by decide⟩).lower ∧ (cell12910 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12910 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12910 ⟨34,by decide⟩).lower ∧ (cell12910 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12910 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12910 ⟨35,by decide⟩).lower ∧ (cell12910 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12910 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12910 ⟨36,by decide⟩).lower ∧ (cell12910 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12910 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12910 ⟨37,by decide⟩).lower ∧ (cell12910 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12910 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12910 ⟨38,by decide⟩).lower ∧ (cell12910 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12910 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12910 ⟨39,by decide⟩).lower ∧ (cell12910 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12910 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12910 ⟨40,by decide⟩).lower ∧ (cell12910 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12910 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12910 ⟨41,by decide⟩).lower ∧ (cell12910 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12910 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12910 ⟨42,by decide⟩).lower ∧ (cell12910 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12910 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12910 ⟨43,by decide⟩).lower ∧ (cell12910 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12910 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12910 ⟨44,by decide⟩).lower ∧ (cell12910 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12910 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12910 ⟨45,by decide⟩).lower ∧ (cell12910 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12910 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12910 ⟨46,by decide⟩).lower ∧ (cell12910 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12910 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12910 ⟨47,by decide⟩).lower ∧ (cell12910 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12910 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12910 ⟨48,by decide⟩).lower ∧ (cell12910 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12910 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12910 ⟨49,by decide⟩).lower ∧ (cell12910 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12910 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12910 ⟨50,by decide⟩).lower ∧ (cell12910 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12910 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12910 ⟨51,by decide⟩).lower ∧ (cell12910 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12910 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12910 ⟨52,by decide⟩).lower ∧ (cell12910 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12910 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12910 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12910 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12910,cell12910,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12910 i).lower ∧
    (cell12910 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12910 i).upper ≤ (0.532 : ℝ) ∧
    (cell12910 i).centre ≤ (0.1 : ℝ) ∧ (cell12910 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12910 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12910 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12910

/-! The local source numeric instances at 12910 have no network premises. -/
namespace BstLean.Part269.N12910
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12910)
open BstLean.Part268 (cell12910)

noncomputable def sourceNumerics12910 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12910 (cell12910 i)
      scalarRow12910.M scalarRow12910.H scalarRow12910.xi := by
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
    energy_allowance := scalarRow12910.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12910]
    centre_nonneg := (scalarRow12910.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12910])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12910
/-! Actual 12911 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12911 ≤ (1.035512843745 : ℝ) := by
  have hr : (113.626581397136 : ℝ) ≤ √(12911 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.626581397136 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12911 12911 (11 / 1000) ≤
    (0.008412529509 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12911) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.626581397136 : ℝ) ≤ √(12911 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12911)
  have hdiv : K / √(12911 : ℝ) ≤ K / 113.626581397136 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.626581397136 ≤ (0.008412529509 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12911.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12911 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12911 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12911 := gPlus_lower 12911
end BstLean.Part269.N12911

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12911
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035512843744 : ℝ) ≤ wn 12911 := by
  have hn : √(12911 : ℝ) ≤ 113.626581397137 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12911 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.626581397137 ≤ 2 / √(12911 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247693574 : ℝ) ≤ rhoBar 12911 BstLean.Part154.csC ∧
    rhoBar 12911 BstLean.Part154.csC ≤ 0.000247693958 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035512843744 : ℝ) / (1.295212 * 12911) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035512843745 : ℝ) / (1.29521 * 12911) := by gcongr
      _ ≤ (0.000247693958 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12911 BstLean.Part154.csC) ≤ 0.000990837185 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12911 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) ≤ 0.000189190170 ∧
    cc1 (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) ≤ 0.000120382991 ∧
    cc2 (rhoBar 12911 BstLean.Part154.csC) ≤ 0.000069883285 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12911 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12911 BstLean.Part154.csC * nuR (rhoBar 12911 BstLean.Part154.csC)) ≤ 0.000495403255 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247693958 : ℝ) * 0.000990837185 := by gcongr
      _ ≤ (0.000495403255 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12911 BstLean.Part154.csC) * nuR (rhoBar 12911 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990837185 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12911 BstLean.Part154.csC) * rhoBar 12911 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247693958 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247693958 / 2 + 0.399 * 0.000990837185 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189190170 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495403255 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120382991 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247693958 / 1.414213562 := by gcongr
      _ ≤ (0.000069883285 : ℝ) := by norm_num

end BstLean.Part269.N12911

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12911
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) ≤ 1.54573E-7 := by
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12911 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12911 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189190170 : ℝ) ^ 2 + 0.000120382991 ^ 2 + 3 * 0.000069883285 ^ 2 +
        2 * 0.797885 * 0.000189190170 * 0.000120382991 + 2 * 0.000189190170 * 0.000069883285 +
        4 * 0.797885 * 0.000120382991 * 0.000069883285 := by gcongr
    _ ≤ (1.54573E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12911 BstLean.Part154.csC Θ ≤ 0.002584844237 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12911 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12911 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035512843745 * 1.54573E-7 / (0.000247693574 : ℝ) := by gcongr
    _ ≤ 0.002584844237 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12911 BstLean.Part154.csC Θ ≤ 0.002867195384 + 0.000653147258 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12911 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035512843745 : ℝ) * ((2 * Θ * 0.000247693958 +
        (6863 / 10000) * 0.000247693958 * 12911 * 0.000990837185) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002867195384 + 0.000653147258 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12911 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12911 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12911 0.011 Θ ∧ gammaRatio 12911 0.011 Θ ≤ 0.000085150778 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12911 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035512843745 : ℝ) * 0.525 / ((1 - 0.011) * 12911) := by gcongr
      _ ≤ (0.000085150778 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12911 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12911 0.011 Θ) :=
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
    badAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12911 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12911 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12911 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12911 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12911 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12911 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12911 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12911 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12911 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12911 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035512843745 : ℝ) * 12911 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003330866401 + 0.003237991495 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12911

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12911
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12911 BstLean.Part154.csC) (piBar (rhoBar 12911 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12911 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12911 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12911 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12911 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12911 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12911 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12911 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12911 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12911 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052049048413 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12911) ≤ 0.010510195470 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12911 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035512843745)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010510195470 + 2 * 0.737676 / 12911) := by gcongr
    _ ≤ (0.052049048413 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12911 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12911

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12911
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512954395 : ℝ) ≤ plow 12911 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12911) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537411936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357043225) : eMP 12911 0.011 xi bn ≤ 0.001168568995 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12911 : ℝ) * (1 - 0.011))) ≤ 0.000577821523 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001357043225 / (12911 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577821523 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577821523 : ℝ) + 3.141593 * 0.052537411936 / (12911 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168568995 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537411936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357043225) : PiBarMP 12911 12 0.011 xi bn ≤ 0.159914834422 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12911 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036838067607 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.999907079607 : ℝ) ≤ √((12911 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.626581397136 : ℝ) ≤ √(12911 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12911) ≤ 0.122615747931 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036838067607 + 0.052537411936 * 1.772454 / (2 * (112.999907079607 : ℝ))) * (1 + 0.001168568995) +
        8 / (12911 * 113.626581397136) + 0.122615747931 := by gcongr
    _ ≤ (0.159914834422 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537411936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357043225) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281259458160) :
    parallelOracle 12911 0.011 xi bn cd ≤ 0.160888975245 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12911 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12911 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512954395 : ℝ) ≤ plow 12911 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.626581397136 : ℝ) ≤ √(12911 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281259458160 : ℝ) / (2 * 0.560512954395 * 113.626581397136)) * 0.159914834422 +
        0.281259458160 ^ 2 / (2 * 0.560512954395 * 113.626581397136) := by gcongr
    _ ≤ (0.160888975245 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537411936) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001357043225)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281259458160) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12911 12911 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512954395 : ℝ) ≤ plow 12911 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.626581397136 : ℝ) ≤ √(12911 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12911 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12911 Θ 1.22 ≤ 0.011670689057 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.626581397136 := by gcongr <;> linarith
      _ ≤ (0.011670689057 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12911 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12911 12911 0.011 ≤ 0.008412529509 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12911 12911 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12911 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12911 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12911 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12911 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160888975245 + 0.011670689057 + (0.008412529509 : ℝ) *
        (1 + 2 * (0.281259458160 + 0.011670689057) / (0.560512954395 * 113.626581397136))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12911]

end BstLean.Part269.N12911

/-! The original eight local profiles supply actual 12911 moment certificates. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12911 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052537411936 ∧
    0 ≤ bN 12911 BstLean.Part154.csC (groupTheta g) ∧ bN 12911 BstLean.Part154.csC (groupTheta g) ≤ 0.001357043225 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12911 12911 0.011
      (momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12911 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12911 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12911 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229210409747 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12911 0.011
      (momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12911 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12911
/-! The actual computed-centre upper energy formula at 12911. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12911

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12911)
open BstLean.Part268 (cell12911)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084897438887
  | 2 => 0.085829789193
  | 3 => 0.086758843011
  | 4 => 0.087685682201
  | 5 => 0.088611625516
  | 6 => 0.089538265071
  | 7 => 0.090467506483
  | 8 => 0.091401612772
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12911 12911 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12911 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12911

/-! Actual upper energy certificates on all 43 source endpoints at 12911. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12911)
open BstLean.Part268 (cell12911)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12911 (gMinus 12911) (1 - (cell12911 i).lower) ≤ 1 ∧
    energyUpper 12911 (gMinus 12911) (BstLean.Part211.gPlus 12911)
      (finiteEnergy 12911 12911 0.011) (1 - (cell12911 i).lower) ≤
      (cell12911 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨10,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨11,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨12,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨13,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨14,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨15,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨16,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨17,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨18,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨19,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨20,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨21,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨22,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨23,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨24,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨25,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨26,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨27,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨28,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨29,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨30,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨31,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨32,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨33,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨34,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨35,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨36,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨37,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨38,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨39,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨40,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨41,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨42,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨43,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨44,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨45,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨46,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨47,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨48,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨49,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨50,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨51,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12911) (by norm_num)
        (q := 1 - (cell12911 ⟨52,by decide⟩).lower)
        (by norm_num [cell12911]) (by norm_num [cell12911])
      exact ⟨E.1,E.2.trans (by norm_num [cell12911])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12911

/-! Source-cell containment and simple scalar guards at 12911. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12911)
open BstLean.Part268 (cell12911)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12911 ⟨10,by decide⟩).lower ∧ (cell12911 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12911 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12911 ⟨11,by decide⟩).lower ∧ (cell12911 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12911 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12911 ⟨12,by decide⟩).lower ∧ (cell12911 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12911 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12911 ⟨13,by decide⟩).lower ∧ (cell12911 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12911 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12911 ⟨14,by decide⟩).lower ∧ (cell12911 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12911 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12911 ⟨15,by decide⟩).lower ∧ (cell12911 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12911 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12911 ⟨16,by decide⟩).lower ∧ (cell12911 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12911 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12911 ⟨17,by decide⟩).lower ∧ (cell12911 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12911 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12911 ⟨18,by decide⟩).lower ∧ (cell12911 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12911 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12911 ⟨19,by decide⟩).lower ∧ (cell12911 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12911 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12911 ⟨20,by decide⟩).lower ∧ (cell12911 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12911 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12911 ⟨21,by decide⟩).lower ∧ (cell12911 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12911 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12911 ⟨22,by decide⟩).lower ∧ (cell12911 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12911 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12911 ⟨23,by decide⟩).lower ∧ (cell12911 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12911 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12911 ⟨24,by decide⟩).lower ∧ (cell12911 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12911 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12911 ⟨25,by decide⟩).lower ∧ (cell12911 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12911 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12911 ⟨26,by decide⟩).lower ∧ (cell12911 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12911 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12911 ⟨27,by decide⟩).lower ∧ (cell12911 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12911 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12911 ⟨28,by decide⟩).lower ∧ (cell12911 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12911 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12911 ⟨29,by decide⟩).lower ∧ (cell12911 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12911 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12911 ⟨30,by decide⟩).lower ∧ (cell12911 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12911 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12911 ⟨31,by decide⟩).lower ∧ (cell12911 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12911 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12911 ⟨32,by decide⟩).lower ∧ (cell12911 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12911 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12911 ⟨33,by decide⟩).lower ∧ (cell12911 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12911 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12911 ⟨34,by decide⟩).lower ∧ (cell12911 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12911 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12911 ⟨35,by decide⟩).lower ∧ (cell12911 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12911 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12911 ⟨36,by decide⟩).lower ∧ (cell12911 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12911 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12911 ⟨37,by decide⟩).lower ∧ (cell12911 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12911 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12911 ⟨38,by decide⟩).lower ∧ (cell12911 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12911 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12911 ⟨39,by decide⟩).lower ∧ (cell12911 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12911 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12911 ⟨40,by decide⟩).lower ∧ (cell12911 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12911 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12911 ⟨41,by decide⟩).lower ∧ (cell12911 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12911 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12911 ⟨42,by decide⟩).lower ∧ (cell12911 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12911 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12911 ⟨43,by decide⟩).lower ∧ (cell12911 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12911 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12911 ⟨44,by decide⟩).lower ∧ (cell12911 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12911 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12911 ⟨45,by decide⟩).lower ∧ (cell12911 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12911 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12911 ⟨46,by decide⟩).lower ∧ (cell12911 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12911 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12911 ⟨47,by decide⟩).lower ∧ (cell12911 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12911 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12911 ⟨48,by decide⟩).lower ∧ (cell12911 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12911 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12911 ⟨49,by decide⟩).lower ∧ (cell12911 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12911 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12911 ⟨50,by decide⟩).lower ∧ (cell12911 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12911 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12911 ⟨51,by decide⟩).lower ∧ (cell12911 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12911 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12911 ⟨52,by decide⟩).lower ∧ (cell12911 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12911 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12911 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12911 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12911,cell12911,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12911 i).lower ∧
    (cell12911 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12911 i).upper ≤ (0.532 : ℝ) ∧
    (cell12911 i).centre ≤ (0.1 : ℝ) ∧ (cell12911 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12911 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12911 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12911

/-! The local source numeric instances at 12911 have no network premises. -/
namespace BstLean.Part269.N12911
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12911)
open BstLean.Part268 (cell12911)

noncomputable def sourceNumerics12911 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12911 (cell12911 i)
      scalarRow12911.M scalarRow12911.H scalarRow12911.xi := by
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
    energy_allowance := scalarRow12911.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12911]
    centre_nonneg := (scalarRow12911.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12911])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12911
/-! Actual 12912 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12912 ≤ (1.035511456534 : ℝ) := by
  have hr : (113.630981690734 : ℝ) ≤ √(12912 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.630981690734 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12912 12912 (11 / 1000) ≤
    (0.008412203737 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12912) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.630981690734 : ℝ) ≤ √(12912 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12912)
  have hdiv : K / √(12912 : ℝ) ≤ K / 113.630981690734 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.630981690734 ≤ (0.008412203737 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12912.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12912 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12912 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12912 := gPlus_lower 12912
end BstLean.Part269.N12912

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12912
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035511456533 : ℝ) ≤ wn 12912 := by
  have hn : √(12912 : ℝ) ≤ 113.630981690735 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12912 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.630981690735 ≤ 2 / √(12912 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247674059 : ℝ) ≤ rhoBar 12912 BstLean.Part154.csC ∧
    rhoBar 12912 BstLean.Part154.csC ≤ 0.000247674443 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035511456533 : ℝ) / (1.295212 * 12912) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035511456534 : ℝ) / (1.29521 * 12912) := by gcongr
      _ ≤ (0.000247674443 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12912 BstLean.Part154.csC) ≤ 0.000990759115 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12912 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) ≤ 0.000189175263 ∧
    cc1 (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) ≤ 0.000120373506 ∧
    cc2 (rhoBar 12912 BstLean.Part154.csC) ≤ 0.000069877780 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12912 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12912 BstLean.Part154.csC * nuR (rhoBar 12912 BstLean.Part154.csC)) ≤ 0.000495364222 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247674443 : ℝ) * 0.000990759115 := by gcongr
      _ ≤ (0.000495364222 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12912 BstLean.Part154.csC) * nuR (rhoBar 12912 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000990759115 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12912 BstLean.Part154.csC) * rhoBar 12912 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247674443 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247674443 / 2 + 0.399 * 0.000990759115 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189175263 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495364222 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120373506 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247674443 / 1.414213562 := by gcongr
      _ ≤ (0.000069877780 : ℝ) := by norm_num

end BstLean.Part269.N12912

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12912
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) ≤ 1.54548E-7 := by
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12912 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12912 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189175263 : ℝ) ^ 2 + 0.000120373506 ^ 2 + 3 * 0.000069877780 ^ 2 +
        2 * 0.797885 * 0.000189175263 * 0.000120373506 + 2 * 0.000189175263 * 0.000069877780 +
        4 * 0.797885 * 0.000120373506 * 0.000069877780 := by gcongr
    _ ≤ (1.54548E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12912 BstLean.Part154.csC Θ ≤ 0.002584626347 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12912 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12912 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035511456534 * 1.54548E-7 / (0.000247674059 : ℝ) := by gcongr
    _ ≤ 0.002584626347 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12912 BstLean.Part154.csC Θ ≤ 0.002866961791 + 0.000653094924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12912 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035511456534 : ℝ) * ((2 * Θ * 0.000247674443 +
        (6863 / 10000) * 0.000247674443 * 12912 * 0.000990759115) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002866961791 + 0.000653094924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12912 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12912 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12912 0.011 Θ ∧ gammaRatio 12912 0.011 Θ ≤ 0.000085144069 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12912 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035511456534 : ℝ) * 0.525 / ((1 - 0.011) * 12912) := by gcongr
      _ ≤ (0.000085144069 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12912 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12912 0.011 Θ) :=
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
    badAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463671017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12912 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12912 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12912 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12912 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12912 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12912 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12912 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12912 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12912 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12912 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035511456534 : ℝ) * 12912 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463671017 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003330632808 + 0.003237721271 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12912

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12912
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12912 BstLean.Part154.csC) (piBar (rhoBar 12912 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12912 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12912 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12912 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12912 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12912 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12912 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12912 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12912 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12912 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052047011168 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12912) ≤ 0.010509788469 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12912 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035511456534)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010509788469 + 2 * 0.737676 / 12912) := by gcongr
    _ ≤ (0.052047011168 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12912 12 ≤ 0.0015 := by
  exact BstLean.Part269.S22.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12912

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12912
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512998149 : ℝ) ≤ plow 12912 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12912) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537036476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356928833) : eMP 12912 0.011 xi bn ≤ 0.001168474444 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12912 : ℝ) * (1 - 0.011))) ≤ 0.000577774794 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001356928833 / (12912 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577774794 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577774794 : ℝ) + 3.141593 * 0.052537036476 / (12912 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001168474444 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537036476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356928833) : PiBarMP 12912 12 0.011 xi bn ≤ 0.159908508641 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12912 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036836514942 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.004283104668 : ℝ) ≤ √((12912 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.630981690734 : ℝ) ≤ √(12912 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12912) ≤ 0.122610999707 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036836514942 + 0.052537036476 * 1.772454 / (2 * (113.004283104668 : ℝ))) * (1 + 0.001168474444) +
        8 / (12912 * 113.630981690734) + 0.122610999707 := by gcongr
    _ ≤ (0.159908508641 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537036476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356928833) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281256601884) :
    parallelOracle 12912 0.011 xi bn cd ≤ 0.160882581499 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12912 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12912 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512998149 : ℝ) ≤ plow 12912 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.630981690734 : ℝ) ≤ √(12912 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281256601884 : ℝ) / (2 * 0.560512998149 * 113.630981690734)) * 0.159908508641 +
        0.281256601884 ^ 2 / (2 * 0.560512998149 * 113.630981690734) := by gcongr
    _ ≤ (0.160882581499 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052537036476) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001356928833)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281256601884) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12912 12912 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512998149 : ℝ) ≤ plow 12912 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.630981690734 : ℝ) ≤ √(12912 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12912 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12912 Θ 1.22 ≤ 0.011670237116 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.630981690734 := by gcongr <;> linarith
      _ ≤ (0.011670237116 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12912 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12912 12912 0.011 ≤ 0.008412203737 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12912 12912 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12912 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12912 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12912 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12912 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160882581499 + 0.011670237116 + (0.008412203737 : ℝ) *
        (1 + 2 * (0.281256601884 + 0.011670237116) / (0.560512998149 * 113.630981690734))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12912]

end BstLean.Part269.N12912

/-! The original eight local profiles supply actual 12912 moment certificates. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12912 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052537036476 ∧
    0 ≤ bN 12912 BstLean.Part154.csC (groupTheta g) ∧ bN 12912 BstLean.Part154.csC (groupTheta g) ≤ 0.001356928833 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12912 12912 0.011
      (momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12912 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12912 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12912 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229209590716 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12912 0.011
      (momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12912 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12912
/-! The actual computed-centre upper energy formula at 12912. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12912

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12912)
open BstLean.Part268 (cell12912)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084894729374
  | 2 => 0.085827034335
  | 3 => 0.086756036929
  | 4 => 0.087682817614
  | 5 => 0.088608693486
  | 6 => 0.089535254714
  | 7 => 0.090464404647
  | 8 => 0.091398403671
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12912 12912 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12912 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003333438387 + 0.003240843277 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S22.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S22.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12912

/-! Actual upper energy certificates on all 43 source endpoints at 12912. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12912)
open BstLean.Part268 (cell12912)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12912 (gMinus 12912) (1 - (cell12912 i).lower) ≤ 1 ∧
    energyUpper 12912 (gMinus 12912) (BstLean.Part211.gPlus 12912)
      (finiteEnergy 12912 12912 0.011) (1 - (cell12912 i).lower) ≤
      (cell12912 i).energy := by
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
      have E := BstLean.Part269.S22.uniformEnergy10 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨10,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy11 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨11,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy12 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨12,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy13 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨13,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy14 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨14,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy15 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨15,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy16 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨16,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy17 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨17,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy18 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨18,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy19 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨19,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy20 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨20,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy21 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨21,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy22 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨22,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy23 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨23,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy24 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨24,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy25 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨25,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy26 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨26,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy27 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨27,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy28 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨28,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy29 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨29,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy30 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨30,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy31 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨31,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy32 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨32,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy33 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨33,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy34 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨34,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy35 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨35,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy36 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨36,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy37 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨37,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy38 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨38,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy39 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨39,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy40 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨40,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy41 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨41,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy42 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨42,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy43 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨43,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy44 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨44,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy45 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨45,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy46 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨46,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy47 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨47,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy48 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨48,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy49 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨49,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy50 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨50,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy51 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨51,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S22.uniformEnergy52 (n := 12912) (by norm_num)
        (q := 1 - (cell12912 ⟨52,by decide⟩).lower)
        (by norm_num [cell12912]) (by norm_num [cell12912])
      exact ⟨E.1,E.2.trans (by norm_num [cell12912])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12912

/-! Source-cell containment and simple scalar guards at 12912. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12912)
open BstLean.Part268 (cell12912)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12912 ⟨10,by decide⟩).lower ∧ (cell12912 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12912 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12912 ⟨11,by decide⟩).lower ∧ (cell12912 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12912 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12912 ⟨12,by decide⟩).lower ∧ (cell12912 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12912 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12912 ⟨13,by decide⟩).lower ∧ (cell12912 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12912 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12912 ⟨14,by decide⟩).lower ∧ (cell12912 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12912 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12912 ⟨15,by decide⟩).lower ∧ (cell12912 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12912 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12912 ⟨16,by decide⟩).lower ∧ (cell12912 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12912 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12912 ⟨17,by decide⟩).lower ∧ (cell12912 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12912 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12912 ⟨18,by decide⟩).lower ∧ (cell12912 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12912 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12912 ⟨19,by decide⟩).lower ∧ (cell12912 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12912 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12912 ⟨20,by decide⟩).lower ∧ (cell12912 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12912 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12912 ⟨21,by decide⟩).lower ∧ (cell12912 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12912 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12912 ⟨22,by decide⟩).lower ∧ (cell12912 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12912 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12912 ⟨23,by decide⟩).lower ∧ (cell12912 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12912 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12912 ⟨24,by decide⟩).lower ∧ (cell12912 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12912 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12912 ⟨25,by decide⟩).lower ∧ (cell12912 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12912 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12912 ⟨26,by decide⟩).lower ∧ (cell12912 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12912 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12912 ⟨27,by decide⟩).lower ∧ (cell12912 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12912 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12912 ⟨28,by decide⟩).lower ∧ (cell12912 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12912 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12912 ⟨29,by decide⟩).lower ∧ (cell12912 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12912 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12912 ⟨30,by decide⟩).lower ∧ (cell12912 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12912 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12912 ⟨31,by decide⟩).lower ∧ (cell12912 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12912 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12912 ⟨32,by decide⟩).lower ∧ (cell12912 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12912 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12912 ⟨33,by decide⟩).lower ∧ (cell12912 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12912 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12912 ⟨34,by decide⟩).lower ∧ (cell12912 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12912 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12912 ⟨35,by decide⟩).lower ∧ (cell12912 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12912 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12912 ⟨36,by decide⟩).lower ∧ (cell12912 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12912 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12912 ⟨37,by decide⟩).lower ∧ (cell12912 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12912 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12912 ⟨38,by decide⟩).lower ∧ (cell12912 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12912 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12912 ⟨39,by decide⟩).lower ∧ (cell12912 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12912 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12912 ⟨40,by decide⟩).lower ∧ (cell12912 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12912 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12912 ⟨41,by decide⟩).lower ∧ (cell12912 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12912 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12912 ⟨42,by decide⟩).lower ∧ (cell12912 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12912 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12912 ⟨43,by decide⟩).lower ∧ (cell12912 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12912 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12912 ⟨44,by decide⟩).lower ∧ (cell12912 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12912 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12912 ⟨45,by decide⟩).lower ∧ (cell12912 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12912 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12912 ⟨46,by decide⟩).lower ∧ (cell12912 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12912 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12912 ⟨47,by decide⟩).lower ∧ (cell12912 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12912 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12912 ⟨48,by decide⟩).lower ∧ (cell12912 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12912 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12912 ⟨49,by decide⟩).lower ∧ (cell12912 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12912 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12912 ⟨50,by decide⟩).lower ∧ (cell12912 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12912 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12912 ⟨51,by decide⟩).lower ∧ (cell12912 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12912 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12912 ⟨52,by decide⟩).lower ∧ (cell12912 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12912 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12912 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12912 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12912,cell12912,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12912 i).lower ∧
    (cell12912 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12912 i).upper ≤ (0.532 : ℝ) ∧
    (cell12912 i).centre ≤ (0.1 : ℝ) ∧ (cell12912 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12912 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12912 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12912

/-! The local source numeric instances at 12912 have no network premises. -/
namespace BstLean.Part269.N12912
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12912)
open BstLean.Part268 (cell12912)

noncomputable def sourceNumerics12912 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12912 (cell12912 i)
      scalarRow12912.M scalarRow12912.H scalarRow12912.xi := by
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
    energy_allowance := scalarRow12912.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12912]
    centre_nonneg := (scalarRow12912.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D22.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12912])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12912