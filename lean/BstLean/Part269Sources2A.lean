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
import BstLean.Part269Direction2
import BstLean.Part269Shared2
import BstLean.Part269Finite
import BstLean.Part269Rows2
import BstLean.Part269Source
/-! Actual 12400 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12400 ≤ (1.036243641051 : ℝ) := by
  have hr : (111.355287256600 : ℝ) ≤ √(12400 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.355287256600 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12400 12400 (11 / 1000) ≤
    (0.008584119727 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12400) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.355287256600 : ℝ) ≤ √(12400 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12400)
  have hdiv : K / √(12400 : ℝ) ≤ K / 111.355287256600 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.355287256600 ≤ (0.008584119727 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12400.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12400 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12400 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12400 := gPlus_lower 12400
end BstLean.Part269.N12400

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12400
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036243641050 : ℝ) ≤ wn 12400 := by
  have hn : √(12400 : ℝ) ≤ 111.355287256601 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12400 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.355287256601 ≤ 2 / √(12400 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258082956 : ℝ) ≤ rhoBar 12400 BstLean.Part154.csC ∧
    rhoBar 12400 BstLean.Part154.csC ≤ 0.000258083356 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036243641050 : ℝ) / (1.295212 * 12400) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036243641051 : ℝ) / (1.29521 * 12400) := by gcongr
      _ ≤ (0.000258083356 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12400 BstLean.Part154.csC) ≤ 0.001032400032 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12400 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) ≤ 0.000197126034 ∧
    cc1 (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) ≤ 0.000125432558 ∧
    cc2 (rhoBar 12400 BstLean.Part154.csC) ≤ 0.000072814504 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12400 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12400 BstLean.Part154.csC * nuR (rhoBar 12400 BstLean.Part154.csC)) ≤ 0.000516183364 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258083356 : ℝ) * 0.001032400032 := by gcongr
      _ ≤ (0.000516183364 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12400 BstLean.Part154.csC) * nuR (rhoBar 12400 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032400032 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12400 BstLean.Part154.csC) * rhoBar 12400 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258083356 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258083356 / 2 + 0.399 * 0.001032400032 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197126034 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516183364 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125432558 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258083356 / 1.414213562 := by gcongr
      _ ≤ (0.000072814504 : ℝ) := by norm_num

end BstLean.Part269.N12400

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12400
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) ≤ 1.67812E-7 := by
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12400 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12400 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197126034 : ℝ) ^ 2 + 0.000125432558 ^ 2 + 3 * 0.000072814504 ^ 2 +
        2 * 0.797885 * 0.000197126034 * 0.000125432558 + 2 * 0.000197126034 * 0.000072814504 +
        4 * 0.797885 * 0.000125432558 * 0.000072814504 := by gcongr
    _ ≤ (1.67812E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12400 BstLean.Part154.csC Θ ≤ 0.002695166246 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12400 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12400 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036243641051 * 1.67812E-7 / (0.000258082956 : ℝ) := by gcongr
    _ ≤ 0.002695166246 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12400 BstLean.Part154.csC Θ ≤ 0.002991684411 + 0.000681023473 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12400 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036243641051 : ℝ) * ((2 * Θ * 0.000258083356 +
        (6863 / 10000) * 0.000258083356 * 12400 * 0.001032400032) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002991684411 + 0.000681023473 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12400 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12400 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12400 0.011 Θ ∧ gammaRatio 12400 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12400 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036243641051 : ℝ) * 0.525 / ((1 - 0.011) * 12400) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12400 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12400 0.011 Θ) :=
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
    badAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12400 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12400 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12400 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12400 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12400 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12400 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12400 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12400 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12400 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12400 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036243641051 : ℝ) * 12400 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004091684411 + 0.003376189719 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12400

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12400
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12400 BstLean.Part154.csC) (piBar (rhoBar 12400 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12400 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12400 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12400 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12400 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12400 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12400 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12400 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12400 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12400 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053122334932 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12400) ≤ 0.010724570072 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12400 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036243641051)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010724570072 + 2 * 0.737676 / 12400) := by gcongr
    _ ≤ (0.053122334932 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12400 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12400

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12400
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489673169 : ℝ) ≤ plow 12400 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12400) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370784014)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414962280) : eMP 12400 0.011 xi bn ≤ 0.001217788310 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12400 : ℝ) * (1 - 0.011))) ≤ 0.000602058100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414962280 / (12400 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602058100 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602058100 : ℝ) + 3.141593 * 0.053370784014 / (12400 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217788310 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370784014)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414962280) : PiBarMP 12400 12 0.011 xi bn ≤ 0.163211936059 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12400 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037615984369 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.741139600421 : ℝ) ≤ √((12400 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.355287256600 : ℝ) ≤ √(12400 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12400) ≤ 0.125116719700 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037615984369 + 0.053370784014 * 1.772454 / (2 * (110.741139600421 : ℝ))) * (1 + 0.001217788310) +
        8 / (12400 * 111.355287256600) + 0.125116719700 := by gcongr
    _ ≤ (0.163211936059 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370784014)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414962280) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284143511481) :
    parallelOracle 12400 0.011 xi bn cd ≤ 0.164230250775 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12400 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12400 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489673169 : ℝ) ≤ plow 12400 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.355287256600 : ℝ) ≤ √(12400 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284143511481 : ℝ) / (2 * 0.560489673169 * 111.355287256600)) * 0.163211936059 +
        0.284143511481 ^ 2 / (2 * 0.560489673169 * 111.355287256600) := by gcongr
    _ ≤ (0.164230250775 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370784014) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414962280)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284143511481) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12400 12400 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489673169 : ℝ) ≤ plow 12400 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.355287256600 : ℝ) ≤ √(12400 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12400 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12400 Θ 1.22 ≤ 0.011908734042 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.355287256600 := by gcongr <;> linarith
      _ ≤ (0.011908734042 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12400 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12400 12400 0.011 ≤ 0.008584119727 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12400 12400 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12400 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12400 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12400 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12400 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164230250775 + 0.011908734042 + (0.008584119727 : ℝ) *
        (1 + 2 * (0.284143511481 + 0.011908734042) / (0.560489673169 * 111.355287256600))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12400]

end BstLean.Part269.N12400

/-! The original eight local profiles supply actual 12400 moment certificates. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12400 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053370784014 ∧
    0 ≤ bN 12400 BstLean.Part154.csC (groupTheta g) ∧ bN 12400 BstLean.Part154.csC (groupTheta g) ≤ 0.001414962280 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12400 12400 0.011
      (momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12400 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12400 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12400 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231021176549 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12400 0.011
      (momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12400 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12400
/-! The actual computed-centre upper energy formula at 12400. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12400

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12400)
open BstLean.Part268 (cell12400)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086419381836
  | 2 => 0.087380495145
  | 3 => 0.088342629894
  | 4 => 0.089307851922
  | 5 => 0.090278635785
  | 6 => 0.091257922228
  | 7 => 0.092249180484
  | 8 => 0.093256475351
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12400 12400 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12400 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12400

/-! Actual upper energy certificates on all 43 source endpoints at 12400. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12400)
open BstLean.Part268 (cell12400)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12400 (gMinus 12400) (1 - (cell12400 i).lower) ≤ 1 ∧
    energyUpper 12400 (gMinus 12400) (BstLean.Part211.gPlus 12400)
      (finiteEnergy 12400 12400 0.011) (1 - (cell12400 i).lower) ≤
      (cell12400 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨10,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨11,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨12,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨13,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨14,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨15,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨16,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨17,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨18,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨19,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨20,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨21,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨22,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨23,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨24,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨25,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨26,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨27,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨28,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨29,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨30,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨31,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨32,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨33,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨34,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨35,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨36,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨37,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨38,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨39,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨40,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨41,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨42,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨43,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨44,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨45,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨46,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨47,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨48,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨49,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨50,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨51,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12400) (by norm_num)
        (q := 1 - (cell12400 ⟨52,by decide⟩).lower)
        (by norm_num [cell12400]) (by norm_num [cell12400])
      exact ⟨E.1,E.2.trans (by norm_num [cell12400])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12400

/-! Source-cell containment and simple scalar guards at 12400. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12400)
open BstLean.Part268 (cell12400)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12400 ⟨10,by decide⟩).lower ∧ (cell12400 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12400 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12400 ⟨11,by decide⟩).lower ∧ (cell12400 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12400 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12400 ⟨12,by decide⟩).lower ∧ (cell12400 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12400 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12400 ⟨13,by decide⟩).lower ∧ (cell12400 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12400 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12400 ⟨14,by decide⟩).lower ∧ (cell12400 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12400 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12400 ⟨15,by decide⟩).lower ∧ (cell12400 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12400 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12400 ⟨16,by decide⟩).lower ∧ (cell12400 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12400 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12400 ⟨17,by decide⟩).lower ∧ (cell12400 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12400 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12400 ⟨18,by decide⟩).lower ∧ (cell12400 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12400 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12400 ⟨19,by decide⟩).lower ∧ (cell12400 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12400 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12400 ⟨20,by decide⟩).lower ∧ (cell12400 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12400 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12400 ⟨21,by decide⟩).lower ∧ (cell12400 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12400 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12400 ⟨22,by decide⟩).lower ∧ (cell12400 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12400 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12400 ⟨23,by decide⟩).lower ∧ (cell12400 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12400 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12400 ⟨24,by decide⟩).lower ∧ (cell12400 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12400 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12400 ⟨25,by decide⟩).lower ∧ (cell12400 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12400 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12400 ⟨26,by decide⟩).lower ∧ (cell12400 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12400 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12400 ⟨27,by decide⟩).lower ∧ (cell12400 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12400 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12400 ⟨28,by decide⟩).lower ∧ (cell12400 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12400 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12400 ⟨29,by decide⟩).lower ∧ (cell12400 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12400 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12400 ⟨30,by decide⟩).lower ∧ (cell12400 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12400 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12400 ⟨31,by decide⟩).lower ∧ (cell12400 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12400 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12400 ⟨32,by decide⟩).lower ∧ (cell12400 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12400 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12400 ⟨33,by decide⟩).lower ∧ (cell12400 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12400 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12400 ⟨34,by decide⟩).lower ∧ (cell12400 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12400 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12400 ⟨35,by decide⟩).lower ∧ (cell12400 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12400 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12400 ⟨36,by decide⟩).lower ∧ (cell12400 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12400 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12400 ⟨37,by decide⟩).lower ∧ (cell12400 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12400 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12400 ⟨38,by decide⟩).lower ∧ (cell12400 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12400 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12400 ⟨39,by decide⟩).lower ∧ (cell12400 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12400 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12400 ⟨40,by decide⟩).lower ∧ (cell12400 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12400 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12400 ⟨41,by decide⟩).lower ∧ (cell12400 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12400 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12400 ⟨42,by decide⟩).lower ∧ (cell12400 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12400 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12400 ⟨43,by decide⟩).lower ∧ (cell12400 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12400 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12400 ⟨44,by decide⟩).lower ∧ (cell12400 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12400 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12400 ⟨45,by decide⟩).lower ∧ (cell12400 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12400 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12400 ⟨46,by decide⟩).lower ∧ (cell12400 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12400 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12400 ⟨47,by decide⟩).lower ∧ (cell12400 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12400 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12400 ⟨48,by decide⟩).lower ∧ (cell12400 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12400 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12400 ⟨49,by decide⟩).lower ∧ (cell12400 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12400 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12400 ⟨50,by decide⟩).lower ∧ (cell12400 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12400 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12400 ⟨51,by decide⟩).lower ∧ (cell12400 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12400 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12400 ⟨52,by decide⟩).lower ∧ (cell12400 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12400 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12400 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12400 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12400,cell12400,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12400 i).lower ∧
    (cell12400 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12400 i).upper ≤ (0.532 : ℝ) ∧
    (cell12400 i).centre ≤ (0.1 : ℝ) ∧ (cell12400 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12400 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12400 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12400

/-! The local source numeric instances at 12400 have no network premises. -/
namespace BstLean.Part269.N12400
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12400)
open BstLean.Part268 (cell12400)

noncomputable def sourceNumerics12400 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12400 (cell12400 i)
      scalarRow12400.M scalarRow12400.H scalarRow12400.xi := by
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
    energy_allowance := scalarRow12400.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12400]
    centre_nonneg := (scalarRow12400.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12400])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12400
/-! Actual 12401 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12401 ≤ (1.036242166696 : ℝ) := by
  have hr : (111.359777298627 : ℝ) ≤ √(12401 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.359777298627 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12401 12401 (11 / 1000) ≤
    (0.008583773611 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12401) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.359777298627 : ℝ) ≤ √(12401 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12401)
  have hdiv : K / √(12401 : ℝ) ≤ K / 111.359777298627 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.359777298627 ≤ (0.008583773611 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12401.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12401 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12401 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12401 := gPlus_lower 12401
end BstLean.Part269.N12401

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12401
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036242166695 : ℝ) ≤ wn 12401 := by
  have hn : √(12401 : ℝ) ≤ 111.359777298628 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12401 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.359777298628 ≤ 2 / √(12401 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258061777 : ℝ) ≤ rhoBar 12401 BstLean.Part154.csC ∧
    rhoBar 12401 BstLean.Part154.csC ≤ 0.000258062177 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036242166695 : ℝ) / (1.295212 * 12401) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036242166696 : ℝ) / (1.29521 * 12401) := by gcongr
      _ ≤ (0.000258062177 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12401 BstLean.Part154.csC) ≤ 0.001032315305 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12401 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) ≤ 0.000197109857 ∧
    cc1 (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) ≤ 0.000125422264 ∧
    cc2 (rhoBar 12401 BstLean.Part154.csC) ≤ 0.000072808529 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12401 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12401 BstLean.Part154.csC * nuR (rhoBar 12401 BstLean.Part154.csC)) ≤ 0.000516141003 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258062177 : ℝ) * 0.001032315305 := by gcongr
      _ ≤ (0.000516141003 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12401 BstLean.Part154.csC) * nuR (rhoBar 12401 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032315305 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12401 BstLean.Part154.csC) * rhoBar 12401 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258062177 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258062177 / 2 + 0.399 * 0.001032315305 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197109857 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516141003 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125422264 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258062177 / 1.414213562 := by gcongr
      _ ≤ (0.000072808529 : ℝ) := by norm_num

end BstLean.Part269.N12401

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12401
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) ≤ 1.67784E-7 := by
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12401 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12401 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197109857 : ℝ) ^ 2 + 0.000125422264 ^ 2 + 3 * 0.000072808529 ^ 2 +
        2 * 0.797885 * 0.000197109857 * 0.000125422264 + 2 * 0.000197109857 * 0.000072808529 +
        4 * 0.797885 * 0.000125422264 * 0.000072808529 := by gcongr
    _ ≤ (1.67784E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12401 BstLean.Part154.csC Θ ≤ 0.002694933868 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12401 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12401 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036242166696 * 1.67784E-7 / (0.000258061777 : ℝ) := by gcongr
    _ ≤ 0.002694933868 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12401 BstLean.Part154.csC Θ ≤ 0.002991430373 + 0.000680966617 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12401 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036242166696 : ℝ) * ((2 * Θ * 0.000258062177 +
        (6863 / 10000) * 0.000258062177 * 12401 * 0.001032315305) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002991430373 + 0.000680966617 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12401 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12401 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12401 0.011 Θ ∧ gammaRatio 12401 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12401 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036242166696 : ℝ) * 0.525 / ((1 - 0.011) * 12401) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12401 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12401 0.011 Θ) :=
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
    badAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12401 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12401 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12401 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12401 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12401 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12401 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12401 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12401 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12401 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12401 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036242166696 : ℝ) * 12401 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004091430373 + 0.003375900485 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12401

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12401
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12401 BstLean.Part154.csC) (piBar (rhoBar 12401 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12401 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12401 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12401 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12401 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12401 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12401 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12401 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12401 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12401 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053120169532 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12401) ≤ 0.010724137656 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12401 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036242166696)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010724137656 + 2 * 0.737676 / 12401) := by gcongr
    _ ≤ (0.053120169532 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12401 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12401

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12401
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489720603 : ℝ) ≤ plow 12401 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12401) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370378128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414840281) : eMP 12401 0.011 xi bn ≤ 0.001217686643 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12401 : ℝ) * (1 - 0.011))) ≤ 0.000602007870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414840281 / (12401 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602007870 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602007870 : ℝ) + 3.141593 * 0.053370378128 / (12401 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217686643 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370378128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414840281) : PiBarMP 12401 12 0.011 xi bn ≤ 0.163205242624 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12401 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037614362696 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.745604878929 : ℝ) ≤ √((12401 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.359777298627 : ℝ) ≤ √(12401 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12401) ≤ 0.125111674976 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037614362696 + 0.053370378128 * 1.772454 / (2 * (110.745604878929 : ℝ))) * (1 + 0.001217686643) +
        8 / (12401 * 111.359777298627) + 0.125111674976 := by gcongr
    _ ≤ (0.163205242624 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370378128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414840281) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284140467619) :
    parallelOracle 12401 0.011 xi bn cd ≤ 0.164223483124 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12401 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12401 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489720603 : ℝ) ≤ plow 12401 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.359777298627 : ℝ) ≤ √(12401 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284140467619 : ℝ) / (2 * 0.560489720603 * 111.359777298627)) * 0.163205242624 +
        0.284140467619 ^ 2 / (2 * 0.560489720603 * 111.359777298627) := by gcongr
    _ ≤ (0.164223483124 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053370378128) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414840281)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284140467619) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12401 12401 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489720603 : ℝ) ≤ plow 12401 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.359777298627 : ℝ) ≤ √(12401 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12401 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12401 Θ 1.22 ≤ 0.011908253880 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.359777298627 := by gcongr <;> linarith
      _ ≤ (0.011908253880 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12401 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12401 12401 0.011 ≤ 0.008583773611 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12401 12401 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12401 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12401 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12401 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12401 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164223483124 + 0.011908253880 + (0.008583773611 : ℝ) *
        (1 + 2 * (0.284140467619 + 0.011908253880) / (0.560489720603 * 111.359777298627))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12401]

end BstLean.Part269.N12401

/-! The original eight local profiles supply actual 12401 moment certificates. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12401 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053370378128 ∧
    0 ≤ bN 12401 BstLean.Part154.csC (groupTheta g) ∧ bN 12401 BstLean.Part154.csC (groupTheta g) ≤ 0.001414840281 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12401 12401 0.011
      (momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12401 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12401 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12401 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231020298087 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12401 0.011
      (momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12401 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12401
/-! The actual computed-centre upper energy formula at 12401. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12401

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12401)
open BstLean.Part268 (cell12401)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086416084626
  | 2 => 0.087377128055
  | 3 => 0.088339181291
  | 4 => 0.089304307616
  | 5 => 0.090274978593
  | 6 => 0.091254131498
  | 7 => 0.092245231560
  | 8 => 0.093252338987
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12401 12401 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12401 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12401

/-! Actual upper energy certificates on all 43 source endpoints at 12401. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12401)
open BstLean.Part268 (cell12401)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12401 (gMinus 12401) (1 - (cell12401 i).lower) ≤ 1 ∧
    energyUpper 12401 (gMinus 12401) (BstLean.Part211.gPlus 12401)
      (finiteEnergy 12401 12401 0.011) (1 - (cell12401 i).lower) ≤
      (cell12401 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨10,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨11,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨12,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨13,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨14,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨15,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨16,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨17,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨18,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨19,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨20,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨21,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨22,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨23,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨24,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨25,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨26,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨27,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨28,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨29,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨30,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨31,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨32,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨33,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨34,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨35,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨36,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨37,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨38,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨39,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨40,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨41,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨42,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨43,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨44,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨45,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨46,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨47,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨48,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨49,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨50,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨51,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12401) (by norm_num)
        (q := 1 - (cell12401 ⟨52,by decide⟩).lower)
        (by norm_num [cell12401]) (by norm_num [cell12401])
      exact ⟨E.1,E.2.trans (by norm_num [cell12401])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12401

/-! Source-cell containment and simple scalar guards at 12401. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12401)
open BstLean.Part268 (cell12401)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12401 ⟨10,by decide⟩).lower ∧ (cell12401 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12401 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12401 ⟨11,by decide⟩).lower ∧ (cell12401 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12401 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12401 ⟨12,by decide⟩).lower ∧ (cell12401 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12401 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12401 ⟨13,by decide⟩).lower ∧ (cell12401 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12401 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12401 ⟨14,by decide⟩).lower ∧ (cell12401 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12401 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12401 ⟨15,by decide⟩).lower ∧ (cell12401 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12401 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12401 ⟨16,by decide⟩).lower ∧ (cell12401 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12401 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12401 ⟨17,by decide⟩).lower ∧ (cell12401 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12401 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12401 ⟨18,by decide⟩).lower ∧ (cell12401 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12401 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12401 ⟨19,by decide⟩).lower ∧ (cell12401 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12401 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12401 ⟨20,by decide⟩).lower ∧ (cell12401 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12401 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12401 ⟨21,by decide⟩).lower ∧ (cell12401 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12401 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12401 ⟨22,by decide⟩).lower ∧ (cell12401 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12401 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12401 ⟨23,by decide⟩).lower ∧ (cell12401 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12401 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12401 ⟨24,by decide⟩).lower ∧ (cell12401 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12401 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12401 ⟨25,by decide⟩).lower ∧ (cell12401 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12401 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12401 ⟨26,by decide⟩).lower ∧ (cell12401 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12401 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12401 ⟨27,by decide⟩).lower ∧ (cell12401 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12401 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12401 ⟨28,by decide⟩).lower ∧ (cell12401 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12401 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12401 ⟨29,by decide⟩).lower ∧ (cell12401 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12401 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12401 ⟨30,by decide⟩).lower ∧ (cell12401 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12401 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12401 ⟨31,by decide⟩).lower ∧ (cell12401 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12401 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12401 ⟨32,by decide⟩).lower ∧ (cell12401 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12401 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12401 ⟨33,by decide⟩).lower ∧ (cell12401 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12401 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12401 ⟨34,by decide⟩).lower ∧ (cell12401 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12401 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12401 ⟨35,by decide⟩).lower ∧ (cell12401 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12401 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12401 ⟨36,by decide⟩).lower ∧ (cell12401 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12401 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12401 ⟨37,by decide⟩).lower ∧ (cell12401 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12401 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12401 ⟨38,by decide⟩).lower ∧ (cell12401 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12401 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12401 ⟨39,by decide⟩).lower ∧ (cell12401 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12401 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12401 ⟨40,by decide⟩).lower ∧ (cell12401 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12401 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12401 ⟨41,by decide⟩).lower ∧ (cell12401 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12401 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12401 ⟨42,by decide⟩).lower ∧ (cell12401 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12401 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12401 ⟨43,by decide⟩).lower ∧ (cell12401 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12401 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12401 ⟨44,by decide⟩).lower ∧ (cell12401 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12401 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12401 ⟨45,by decide⟩).lower ∧ (cell12401 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12401 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12401 ⟨46,by decide⟩).lower ∧ (cell12401 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12401 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12401 ⟨47,by decide⟩).lower ∧ (cell12401 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12401 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12401 ⟨48,by decide⟩).lower ∧ (cell12401 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12401 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12401 ⟨49,by decide⟩).lower ∧ (cell12401 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12401 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12401 ⟨50,by decide⟩).lower ∧ (cell12401 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12401 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12401 ⟨51,by decide⟩).lower ∧ (cell12401 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12401 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12401 ⟨52,by decide⟩).lower ∧ (cell12401 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12401 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12401 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12401 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12401,cell12401,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12401 i).lower ∧
    (cell12401 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12401 i).upper ≤ (0.532 : ℝ) ∧
    (cell12401 i).centre ≤ (0.1 : ℝ) ∧ (cell12401 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12401 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12401 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12401

/-! The local source numeric instances at 12401 have no network premises. -/
namespace BstLean.Part269.N12401
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12401)
open BstLean.Part268 (cell12401)

noncomputable def sourceNumerics12401 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12401 (cell12401 i)
      scalarRow12401.M scalarRow12401.H scalarRow12401.xi := by
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
    energy_allowance := scalarRow12401.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12401]
    centre_nonneg := (scalarRow12401.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12401])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12401
/-! Actual 12402 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12402 ≤ (1.036240692521 : ℝ) := by
  have hr : (111.364267159623 : ℝ) ≤ √(12402 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.364267159623 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12402 12402 (11 / 1000) ≤
    (0.008583427537 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12402) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.364267159623 : ℝ) ≤ √(12402 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12402)
  have hdiv : K / √(12402 : ℝ) ≤ K / 111.364267159623 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.364267159623 ≤ (0.008583427537 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12402.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12402 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12402 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12402 := gPlus_lower 12402
end BstLean.Part269.N12402

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12402
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036240692520 : ℝ) ≤ wn 12402 := by
  have hn : √(12402 : ℝ) ≤ 111.364267159624 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12402 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.364267159624 ≤ 2 / √(12402 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258040602 : ℝ) ≤ rhoBar 12402 BstLean.Part154.csC ∧
    rhoBar 12402 BstLean.Part154.csC ≤ 0.000258041002 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036240692520 : ℝ) / (1.295212 * 12402) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036240692521 : ℝ) / (1.29521 * 12402) := by gcongr
      _ ≤ (0.000258041002 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12402 BstLean.Part154.csC) ≤ 0.001032230594 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12402 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) ≤ 0.000197093682 ∧
    cc1 (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) ≤ 0.000125411973 ∧
    cc2 (rhoBar 12402 BstLean.Part154.csC) ≤ 0.000072802555 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12402 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12402 BstLean.Part154.csC * nuR (rhoBar 12402 BstLean.Part154.csC)) ≤ 0.000516098651 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258041002 : ℝ) * 0.001032230594 := by gcongr
      _ ≤ (0.000516098651 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12402 BstLean.Part154.csC) * nuR (rhoBar 12402 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032230594 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12402 BstLean.Part154.csC) * rhoBar 12402 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258041002 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258041002 / 2 + 0.399 * 0.001032230594 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197093682 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516098651 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125411973 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258041002 / 1.414213562 := by gcongr
      _ ≤ (0.000072802555 : ℝ) := by norm_num

end BstLean.Part269.N12402

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12402
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) ≤ 1.67757E-7 := by
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12402 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12402 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197093682 : ℝ) ^ 2 + 0.000125411973 ^ 2 + 3 * 0.000072802555 ^ 2 +
        2 * 0.797885 * 0.000197093682 * 0.000125411973 + 2 * 0.000197093682 * 0.000072802555 +
        4 * 0.797885 * 0.000125411973 * 0.000072802555 := by gcongr
    _ ≤ (1.67757E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12402 BstLean.Part154.csC Θ ≤ 0.002694717475 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12402 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12402 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036240692521 * 1.67757E-7 / (0.000258040602 : ℝ) := by gcongr
    _ ≤ 0.002694717475 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12402 BstLean.Part154.csC Θ ≤ 0.002991176390 + 0.000680909773 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12402 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036240692521 : ℝ) * ((2 * Θ * 0.000258041002 +
        (6863 / 10000) * 0.000258041002 * 12402 * 0.001032230594) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002991176390 + 0.000680909773 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12402 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12402 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12402 0.011 Θ ∧ gammaRatio 12402 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12402 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036240692521 : ℝ) * 0.525 / ((1 - 0.011) * 12402) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12402 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12402 0.011 Θ) :=
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
    badAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12402 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12402 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12402 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12402 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12402 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12402 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12402 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12402 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12402 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12402 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036240692521 : ℝ) * 12402 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004091176390 + 0.003375627248 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12402

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12402
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12402 BstLean.Part154.csC) (piBar (rhoBar 12402 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12402 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12402 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12402 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12402 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12402 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12402 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12402 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12402 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12402 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053118004394 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12402) ≤ 0.010723705292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12402 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036240692521)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010723705292 + 2 * 0.737676 / 12402) := by gcongr
    _ ≤ (0.053118004394 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12402 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12402

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12402
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489768029 : ℝ) ≤ plow 12402 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12402) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369980696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414726675) : eMP 12402 0.011 xi bn ≤ 0.001217588559 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12402 : ℝ) * (1 - 0.011))) ≤ 0.000601959430 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414726675 / (12402 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601959430 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601959430 : ℝ) + 3.141593 * 0.053369980696 / (12402 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217588559 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369980696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414726675) : PiBarMP 12402 12 0.011 xi bn ≤ 0.163198661645 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12402 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037612852525 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.750069977404 : ℝ) ≤ √((12402 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.364267159623 : ℝ) ≤ √(12402 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12402) ≤ 0.125106630862 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037612852525 + 0.053369980696 * 1.772454 / (2 * (110.750069977404 : ℝ))) * (1 + 0.001217588559) +
        8 / (12402 * 111.364267159623) + 0.125106630862 := by gcongr
    _ ≤ (0.163198661645 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369980696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414726675) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284137442313) :
    parallelOracle 12402 0.011 xi bn cd ≤ 0.164216828301 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12402 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12402 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489768029 : ℝ) ≤ plow 12402 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.364267159623 : ℝ) ≤ √(12402 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284137442313 : ℝ) / (2 * 0.560489768029 * 111.364267159623)) * 0.163198661645 +
        0.284137442313 ^ 2 / (2 * 0.560489768029 * 111.364267159623) := by gcongr
    _ ≤ (0.164216828301 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369980696) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414726675)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284137442313) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12402 12402 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489768029 : ℝ) ≤ plow 12402 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.364267159623 : ℝ) ≤ √(12402 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12402 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12402 Θ 1.22 ≤ 0.011907773776 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.364267159623 := by gcongr <;> linarith
      _ ≤ (0.011907773776 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12402 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12402 12402 0.011 ≤ 0.008583427537 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12402 12402 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12402 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12402 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12402 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12402 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164216828301 + 0.011907773776 + (0.008583427537 : ℝ) *
        (1 + 2 * (0.284137442313 + 0.011907773776) / (0.560489768029 * 111.364267159623))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12402]

end BstLean.Part269.N12402

/-! The original eight local profiles supply actual 12402 moment certificates. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12402 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053369980696 ∧
    0 ≤ bN 12402 BstLean.Part154.csC (groupTheta g) ∧ bN 12402 BstLean.Part154.csC (groupTheta g) ≤ 0.001414726675 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12402 12402 0.011
      (momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12402 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12402 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12402 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231019437919 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12402 0.011
      (momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12402 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12402
/-! The actual computed-centre upper energy formula at 12402. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12402

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12402)
open BstLean.Part268 (cell12402)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086412788901
  | 2 => 0.087373762515
  | 3 => 0.088335734320
  | 4 => 0.089300765040
  | 5 => 0.090271323254
  | 6 => 0.091250342767
  | 7 => 0.092241284812
  | 8 => 0.093248205011
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12402 12402 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12402 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12402

/-! Actual upper energy certificates on all 43 source endpoints at 12402. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12402)
open BstLean.Part268 (cell12402)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12402 (gMinus 12402) (1 - (cell12402 i).lower) ≤ 1 ∧
    energyUpper 12402 (gMinus 12402) (BstLean.Part211.gPlus 12402)
      (finiteEnergy 12402 12402 0.011) (1 - (cell12402 i).lower) ≤
      (cell12402 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨10,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨11,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨12,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨13,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨14,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨15,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨16,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨17,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨18,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨19,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨20,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨21,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨22,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨23,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨24,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨25,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨26,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨27,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨28,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨29,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨30,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨31,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨32,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨33,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨34,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨35,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨36,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨37,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨38,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨39,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨40,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨41,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨42,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨43,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨44,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨45,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨46,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨47,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨48,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨49,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨50,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨51,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12402) (by norm_num)
        (q := 1 - (cell12402 ⟨52,by decide⟩).lower)
        (by norm_num [cell12402]) (by norm_num [cell12402])
      exact ⟨E.1,E.2.trans (by norm_num [cell12402])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12402

/-! Source-cell containment and simple scalar guards at 12402. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12402)
open BstLean.Part268 (cell12402)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12402 ⟨10,by decide⟩).lower ∧ (cell12402 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12402 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12402 ⟨11,by decide⟩).lower ∧ (cell12402 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12402 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12402 ⟨12,by decide⟩).lower ∧ (cell12402 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12402 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12402 ⟨13,by decide⟩).lower ∧ (cell12402 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12402 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12402 ⟨14,by decide⟩).lower ∧ (cell12402 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12402 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12402 ⟨15,by decide⟩).lower ∧ (cell12402 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12402 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12402 ⟨16,by decide⟩).lower ∧ (cell12402 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12402 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12402 ⟨17,by decide⟩).lower ∧ (cell12402 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12402 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12402 ⟨18,by decide⟩).lower ∧ (cell12402 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12402 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12402 ⟨19,by decide⟩).lower ∧ (cell12402 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12402 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12402 ⟨20,by decide⟩).lower ∧ (cell12402 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12402 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12402 ⟨21,by decide⟩).lower ∧ (cell12402 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12402 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12402 ⟨22,by decide⟩).lower ∧ (cell12402 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12402 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12402 ⟨23,by decide⟩).lower ∧ (cell12402 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12402 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12402 ⟨24,by decide⟩).lower ∧ (cell12402 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12402 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12402 ⟨25,by decide⟩).lower ∧ (cell12402 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12402 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12402 ⟨26,by decide⟩).lower ∧ (cell12402 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12402 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12402 ⟨27,by decide⟩).lower ∧ (cell12402 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12402 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12402 ⟨28,by decide⟩).lower ∧ (cell12402 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12402 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12402 ⟨29,by decide⟩).lower ∧ (cell12402 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12402 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12402 ⟨30,by decide⟩).lower ∧ (cell12402 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12402 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12402 ⟨31,by decide⟩).lower ∧ (cell12402 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12402 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12402 ⟨32,by decide⟩).lower ∧ (cell12402 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12402 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12402 ⟨33,by decide⟩).lower ∧ (cell12402 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12402 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12402 ⟨34,by decide⟩).lower ∧ (cell12402 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12402 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12402 ⟨35,by decide⟩).lower ∧ (cell12402 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12402 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12402 ⟨36,by decide⟩).lower ∧ (cell12402 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12402 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12402 ⟨37,by decide⟩).lower ∧ (cell12402 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12402 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12402 ⟨38,by decide⟩).lower ∧ (cell12402 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12402 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12402 ⟨39,by decide⟩).lower ∧ (cell12402 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12402 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12402 ⟨40,by decide⟩).lower ∧ (cell12402 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12402 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12402 ⟨41,by decide⟩).lower ∧ (cell12402 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12402 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12402 ⟨42,by decide⟩).lower ∧ (cell12402 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12402 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12402 ⟨43,by decide⟩).lower ∧ (cell12402 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12402 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12402 ⟨44,by decide⟩).lower ∧ (cell12402 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12402 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12402 ⟨45,by decide⟩).lower ∧ (cell12402 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12402 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12402 ⟨46,by decide⟩).lower ∧ (cell12402 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12402 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12402 ⟨47,by decide⟩).lower ∧ (cell12402 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12402 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12402 ⟨48,by decide⟩).lower ∧ (cell12402 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12402 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12402 ⟨49,by decide⟩).lower ∧ (cell12402 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12402 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12402 ⟨50,by decide⟩).lower ∧ (cell12402 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12402 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12402 ⟨51,by decide⟩).lower ∧ (cell12402 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12402 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12402 ⟨52,by decide⟩).lower ∧ (cell12402 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12402 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12402 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12402 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12402,cell12402,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12402 i).lower ∧
    (cell12402 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12402 i).upper ≤ (0.532 : ℝ) ∧
    (cell12402 i).centre ≤ (0.1 : ℝ) ∧ (cell12402 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12402 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12402 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12402

/-! The local source numeric instances at 12402 have no network premises. -/
namespace BstLean.Part269.N12402
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12402)
open BstLean.Part268 (cell12402)

noncomputable def sourceNumerics12402 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12402 (cell12402 i)
      scalarRow12402.M scalarRow12402.H scalarRow12402.xi := by
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
    energy_allowance := scalarRow12402.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12402]
    centre_nonneg := (scalarRow12402.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12402])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12402
/-! Actual 12403 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12403 ≤ (1.036239218525 : ℝ) := by
  have hr : (111.368756839609 : ℝ) ≤ √(12403 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.368756839609 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12403 12403 (11 / 1000) ≤
    (0.008583081505 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12403) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.368756839609 : ℝ) ≤ √(12403 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12403)
  have hdiv : K / √(12403 : ℝ) ≤ K / 111.368756839609 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.368756839609 ≤ (0.008583081505 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12403.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12403 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12403 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12403 := gPlus_lower 12403
end BstLean.Part269.N12403

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12403
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036239218524 : ℝ) ≤ wn 12403 := by
  have hn : √(12403 : ℝ) ≤ 111.368756839610 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12403 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.368756839610 ≤ 2 / √(12403 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258019431 : ℝ) ≤ rhoBar 12403 BstLean.Part154.csC ∧
    rhoBar 12403 BstLean.Part154.csC ≤ 0.000258019830 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036239218524 : ℝ) / (1.295212 * 12403) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036239218525 : ℝ) / (1.29521 * 12403) := by gcongr
      _ ≤ (0.000258019830 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12403 BstLean.Part154.csC) ≤ 0.001032145895 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12403 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) ≤ 0.000197077510 ∧
    cc1 (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) ≤ 0.000125401682 ∧
    cc2 (rhoBar 12403 BstLean.Part154.csC) ≤ 0.000072796582 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12403 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12403 BstLean.Part154.csC * nuR (rhoBar 12403 BstLean.Part154.csC)) ≤ 0.000516056304 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258019830 : ℝ) * 0.001032145895 := by gcongr
      _ ≤ (0.000516056304 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12403 BstLean.Part154.csC) * nuR (rhoBar 12403 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032145895 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12403 BstLean.Part154.csC) * rhoBar 12403 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258019830 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258019830 / 2 + 0.399 * 0.001032145895 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197077510 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516056304 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125401682 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258019830 / 1.414213562 := by gcongr
      _ ≤ (0.000072796582 : ℝ) := by norm_num

end BstLean.Part269.N12403

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12403
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) ≤ 1.67729E-7 := by
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12403 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12403 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197077510 : ℝ) ^ 2 + 0.000125401682 ^ 2 + 3 * 0.000072796582 ^ 2 +
        2 * 0.797885 * 0.000197077510 * 0.000125401682 + 2 * 0.000197077510 * 0.000072796582 +
        4 * 0.797885 * 0.000125401682 * 0.000072796582 := by gcongr
    _ ≤ (1.67729E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12403 BstLean.Part154.csC Θ ≤ 0.002694484942 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12403 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12403 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036239218525 * 1.67729E-7 / (0.000258019431 : ℝ) := by gcongr
    _ ≤ 0.002694484942 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12403 BstLean.Part154.csC Θ ≤ 0.002990922439 + 0.000680852936 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12403 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036239218525 : ℝ) * ((2 * Θ * 0.000258019830 +
        (6863 / 10000) * 0.000258019830 * 12403 * 0.001032145895) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002990922439 + 0.000680852936 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12403 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12403 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12403 0.011 Θ ∧ gammaRatio 12403 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12403 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036239218525 : ℝ) * 0.525 / ((1 - 0.011) * 12403) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12403 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12403 0.011 Θ) :=
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
    badAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12403 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12403 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12403 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12403 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12403 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12403 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12403 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12403 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12403 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12403 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036239218525 : ℝ) * 12403 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004090922439 + 0.003375337878 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12403

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12403
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12403 BstLean.Part154.csC) (piBar (rhoBar 12403 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12403 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12403 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12403 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12403 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12403 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12403 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12403 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12403 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12403 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053115839524 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12403) ≤ 0.010723272981 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12403 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036239218525)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010723272981 + 2 * 0.737676 / 12403) := by gcongr
    _ ≤ (0.053115839524 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12403 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12403

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12403
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489815447 : ℝ) ≤ plow 12403 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12403) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369574825)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414604595) : eMP 12403 0.011 xi bn ≤ 0.001217486875 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12403 : ℝ) * (1 - 0.011))) ≤ 0.000601909191 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414604595 / (12403 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601909191 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601909191 : ℝ) + 3.141593 * 0.053369574825 / (12403 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217486875 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369574825)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414604595) : PiBarMP 12403 12 0.011 xi bn ≤ 0.163191968223 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12403 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037611229640 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.754534895867 : ℝ) ≤ √((12403 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.368756839609 : ℝ) ≤ √(12403 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12403) ≤ 0.125101587359 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037611229640 + 0.053369574825 * 1.772454 / (2 * (110.754534895867 : ℝ))) * (1 + 0.001217486875) +
        8 / (12403 * 111.368756839609) + 0.125101587359 := by gcongr
    _ ≤ (0.163191968223 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369574825)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414604595) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284134399006) :
    parallelOracle 12403 0.011 xi bn cd ≤ 0.164210060681 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12403 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12403 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489815447 : ℝ) ≤ plow 12403 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.368756839609 : ℝ) ≤ √(12403 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284134399006 : ℝ) / (2 * 0.560489815447 * 111.368756839609)) * 0.163191968223 +
        0.284134399006 ^ 2 / (2 * 0.560489815447 * 111.368756839609) := by gcongr
    _ ≤ (0.164210060681 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369574825) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414604595)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284134399006) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12403 12403 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489815447 : ℝ) ≤ plow 12403 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.368756839609 : ℝ) ≤ √(12403 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12403 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12403 Θ 1.22 ≤ 0.011907293730 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.368756839609 := by gcongr <;> linarith
      _ ≤ (0.011907293730 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12403 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12403 12403 0.011 ≤ 0.008583081505 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12403 12403 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12403 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12403 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12403 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12403 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164210060681 + 0.011907293730 + (0.008583081505 : ℝ) *
        (1 + 2 * (0.284134399006 + 0.011907293730) / (0.560489815447 * 111.368756839609))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12403]

end BstLean.Part269.N12403

/-! The original eight local profiles supply actual 12403 moment certificates. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12403 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053369574825 ∧
    0 ≤ bN 12403 BstLean.Part154.csC (groupTheta g) ∧ bN 12403 BstLean.Part154.csC (groupTheta g) ≤ 0.001414604595 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12403 12403 0.011
      (momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12403 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12403 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12403 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231018559482 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12403 0.011
      (momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12403 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12403
/-! The actual computed-centre upper energy formula at 12403. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12403

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12403)
open BstLean.Part268 (cell12403)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086409494659
  | 2 => 0.087370398524
  | 3 => 0.088332288978
  | 4 => 0.089297224194
  | 5 => 0.090267669764
  | 6 => 0.091246556033
  | 7 => 0.092237340237
  | 8 => 0.093244073419
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12403 12403 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12403 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12403

/-! Actual upper energy certificates on all 43 source endpoints at 12403. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12403)
open BstLean.Part268 (cell12403)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12403 (gMinus 12403) (1 - (cell12403 i).lower) ≤ 1 ∧
    energyUpper 12403 (gMinus 12403) (BstLean.Part211.gPlus 12403)
      (finiteEnergy 12403 12403 0.011) (1 - (cell12403 i).lower) ≤
      (cell12403 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨10,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨11,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨12,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨13,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨14,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨15,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨16,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨17,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨18,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨19,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨20,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨21,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨22,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨23,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨24,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨25,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨26,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨27,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨28,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨29,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨30,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨31,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨32,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨33,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨34,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨35,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨36,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨37,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨38,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨39,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨40,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨41,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨42,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨43,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨44,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨45,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨46,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨47,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨48,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨49,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨50,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨51,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12403) (by norm_num)
        (q := 1 - (cell12403 ⟨52,by decide⟩).lower)
        (by norm_num [cell12403]) (by norm_num [cell12403])
      exact ⟨E.1,E.2.trans (by norm_num [cell12403])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12403

/-! Source-cell containment and simple scalar guards at 12403. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12403)
open BstLean.Part268 (cell12403)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12403 ⟨10,by decide⟩).lower ∧ (cell12403 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12403 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12403 ⟨11,by decide⟩).lower ∧ (cell12403 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12403 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12403 ⟨12,by decide⟩).lower ∧ (cell12403 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12403 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12403 ⟨13,by decide⟩).lower ∧ (cell12403 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12403 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12403 ⟨14,by decide⟩).lower ∧ (cell12403 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12403 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12403 ⟨15,by decide⟩).lower ∧ (cell12403 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12403 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12403 ⟨16,by decide⟩).lower ∧ (cell12403 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12403 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12403 ⟨17,by decide⟩).lower ∧ (cell12403 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12403 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12403 ⟨18,by decide⟩).lower ∧ (cell12403 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12403 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12403 ⟨19,by decide⟩).lower ∧ (cell12403 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12403 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12403 ⟨20,by decide⟩).lower ∧ (cell12403 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12403 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12403 ⟨21,by decide⟩).lower ∧ (cell12403 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12403 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12403 ⟨22,by decide⟩).lower ∧ (cell12403 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12403 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12403 ⟨23,by decide⟩).lower ∧ (cell12403 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12403 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12403 ⟨24,by decide⟩).lower ∧ (cell12403 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12403 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12403 ⟨25,by decide⟩).lower ∧ (cell12403 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12403 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12403 ⟨26,by decide⟩).lower ∧ (cell12403 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12403 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12403 ⟨27,by decide⟩).lower ∧ (cell12403 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12403 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12403 ⟨28,by decide⟩).lower ∧ (cell12403 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12403 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12403 ⟨29,by decide⟩).lower ∧ (cell12403 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12403 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12403 ⟨30,by decide⟩).lower ∧ (cell12403 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12403 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12403 ⟨31,by decide⟩).lower ∧ (cell12403 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12403 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12403 ⟨32,by decide⟩).lower ∧ (cell12403 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12403 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12403 ⟨33,by decide⟩).lower ∧ (cell12403 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12403 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12403 ⟨34,by decide⟩).lower ∧ (cell12403 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12403 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12403 ⟨35,by decide⟩).lower ∧ (cell12403 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12403 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12403 ⟨36,by decide⟩).lower ∧ (cell12403 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12403 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12403 ⟨37,by decide⟩).lower ∧ (cell12403 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12403 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12403 ⟨38,by decide⟩).lower ∧ (cell12403 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12403 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12403 ⟨39,by decide⟩).lower ∧ (cell12403 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12403 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12403 ⟨40,by decide⟩).lower ∧ (cell12403 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12403 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12403 ⟨41,by decide⟩).lower ∧ (cell12403 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12403 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12403 ⟨42,by decide⟩).lower ∧ (cell12403 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12403 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12403 ⟨43,by decide⟩).lower ∧ (cell12403 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12403 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12403 ⟨44,by decide⟩).lower ∧ (cell12403 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12403 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12403 ⟨45,by decide⟩).lower ∧ (cell12403 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12403 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12403 ⟨46,by decide⟩).lower ∧ (cell12403 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12403 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12403 ⟨47,by decide⟩).lower ∧ (cell12403 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12403 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12403 ⟨48,by decide⟩).lower ∧ (cell12403 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12403 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12403 ⟨49,by decide⟩).lower ∧ (cell12403 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12403 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12403 ⟨50,by decide⟩).lower ∧ (cell12403 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12403 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12403 ⟨51,by decide⟩).lower ∧ (cell12403 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12403 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12403 ⟨52,by decide⟩).lower ∧ (cell12403 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12403 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12403 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12403 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12403,cell12403,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12403 i).lower ∧
    (cell12403 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12403 i).upper ≤ (0.532 : ℝ) ∧
    (cell12403 i).centre ≤ (0.1 : ℝ) ∧ (cell12403 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12403 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12403 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12403

/-! The local source numeric instances at 12403 have no network premises. -/
namespace BstLean.Part269.N12403
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12403)
open BstLean.Part268 (cell12403)

noncomputable def sourceNumerics12403 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12403 (cell12403 i)
      scalarRow12403.M scalarRow12403.H scalarRow12403.xi := by
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
    energy_allowance := scalarRow12403.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12403]
    centre_nonneg := (scalarRow12403.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12403])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12403
/-! Actual 12404 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12404 ≤ (1.036237744708 : ℝ) := by
  have hr : (111.373246338606 : ℝ) ≤ √(12404 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.373246338606 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12404 12404 (11 / 1000) ≤
    (0.008582735515 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12404) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.373246338606 : ℝ) ≤ √(12404 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12404)
  have hdiv : K / √(12404 : ℝ) ≤ K / 111.373246338606 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.373246338606 ≤ (0.008582735515 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12404.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12404 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12404 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12404 := gPlus_lower 12404
end BstLean.Part269.N12404

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12404
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036237744707 : ℝ) ≤ wn 12404 := by
  have hn : √(12404 : ℝ) ≤ 111.373246338607 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12404 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.373246338607 ≤ 2 / √(12404 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257998262 : ℝ) ≤ rhoBar 12404 BstLean.Part154.csC ∧
    rhoBar 12404 BstLean.Part154.csC ≤ 0.000257998662 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036237744707 : ℝ) / (1.295212 * 12404) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036237744708 : ℝ) / (1.29521 * 12404) := by gcongr
      _ ≤ (0.000257998662 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12404 BstLean.Part154.csC) ≤ 0.001032061212 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12404 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) ≤ 0.000197061341 ∧
    cc1 (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) ≤ 0.000125391394 ∧
    cc2 (rhoBar 12404 BstLean.Part154.csC) ≤ 0.000072790609 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12404 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12404 BstLean.Part154.csC * nuR (rhoBar 12404 BstLean.Part154.csC)) ≤ 0.000516013965 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257998662 : ℝ) * 0.001032061212 := by gcongr
      _ ≤ (0.000516013965 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12404 BstLean.Part154.csC) * nuR (rhoBar 12404 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032061212 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12404 BstLean.Part154.csC) * rhoBar 12404 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257998662 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257998662 / 2 + 0.399 * 0.001032061212 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197061341 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516013965 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125391394 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257998662 / 1.414213562 := by gcongr
      _ ≤ (0.000072790609 : ℝ) := by norm_num

end BstLean.Part269.N12404

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12404
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) ≤ 1.67702E-7 := by
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12404 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12404 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197061341 : ℝ) ^ 2 + 0.000125391394 ^ 2 + 3 * 0.000072790609 ^ 2 +
        2 * 0.797885 * 0.000197061341 * 0.000125391394 + 2 * 0.000197061341 * 0.000072790609 +
        4 * 0.797885 * 0.000125391394 * 0.000072790609 := by gcongr
    _ ≤ (1.67702E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12404 BstLean.Part154.csC Θ ≤ 0.002694268418 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12404 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12404 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036237744708 * 1.67702E-7 / (0.000257998262 : ℝ) := by gcongr
    _ ≤ 0.002694268418 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12404 BstLean.Part154.csC Θ ≤ 0.002990668544 + 0.000680796111 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12404 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036237744708 : ℝ) * ((2 * Θ * 0.000257998662 +
        (6863 / 10000) * 0.000257998662 * 12404 * 0.001032061212) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002990668544 + 0.000680796111 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12404 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12404 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12404 0.011 Θ ∧ gammaRatio 12404 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12404 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036237744708 : ℝ) * 0.525 / ((1 - 0.011) * 12404) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12404 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12404 0.011 Θ) :=
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
    badAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12404 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12404 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12404 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12404 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12404 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12404 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12404 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12404 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12404 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12404 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036237744708 : ℝ) * 12404 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004090668544 + 0.003375064529 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12404

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12404
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12404 BstLean.Part154.csC) (piBar (rhoBar 12404 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12404 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12404 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12404 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12404 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12404 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12404 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12404 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12404 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12404 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053113674911 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12404) ≤ 0.010722840721 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12404 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036237744708)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010722840721 + 2 * 0.737676 / 12404) := by gcongr
    _ ≤ (0.053113674911 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12404 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12404

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12404
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489862858 : ℝ) ≤ plow 12404 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12404) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369177422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414490920) : eMP 12404 0.011 xi bn ≤ 0.001217388780 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12404 : ℝ) * (1 - 0.011))) ≤ 0.000601860745 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414490920 / (12404 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601860745 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601860745 : ℝ) + 3.141593 * 0.053369177422 / (12404 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217388780 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369177422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414490920) : PiBarMP 12404 12 0.011 xi bn ≤ 0.163185387424 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12404 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037609718425 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.758999634341 : ℝ) ≤ √((12404 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.373246338606 : ℝ) ≤ √(12404 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12404) ≤ 0.125096544465 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037609718425 + 0.053369177422 * 1.772454 / (2 * (110.758999634341 : ℝ))) * (1 + 0.001217388780) +
        8 / (12404 * 111.373246338606) + 0.125096544465 := by gcongr
    _ ≤ (0.163185387424 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369177422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414490920) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284131374281) :
    parallelOracle 12404 0.011 xi bn cd ≤ 0.164203406058 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12404 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12404 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489862858 : ℝ) ≤ plow 12404 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.373246338606 : ℝ) ≤ √(12404 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284131374281 : ℝ) / (2 * 0.560489862858 * 111.373246338606)) * 0.163185387424 +
        0.284131374281 ^ 2 / (2 * 0.560489862858 * 111.373246338606) := by gcongr
    _ ≤ (0.164203406058 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053369177422) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414490920)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284131374281) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12404 12404 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489862858 : ℝ) ≤ plow 12404 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.373246338606 : ℝ) ≤ √(12404 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12404 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12404 Θ 1.22 ≤ 0.011906813743 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.373246338606 := by gcongr <;> linarith
      _ ≤ (0.011906813743 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12404 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12404 12404 0.011 ≤ 0.008582735515 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12404 12404 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12404 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12404 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12404 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12404 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164203406058 + 0.011906813743 + (0.008582735515 : ℝ) *
        (1 + 2 * (0.284131374281 + 0.011906813743) / (0.560489862858 * 111.373246338606))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12404]

end BstLean.Part269.N12404

/-! The original eight local profiles supply actual 12404 moment certificates. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12404 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053369177422 ∧
    0 ≤ bN 12404 BstLean.Part154.csC (groupTheta g) ∧ bN 12404 BstLean.Part154.csC (groupTheta g) ≤ 0.001414490920 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12404 12404 0.011
      (momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12404 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12404 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12404 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231017699370 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12404 0.011
      (momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12404 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12404
/-! The actual computed-centre upper energy formula at 12404. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12404

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12404)
open BstLean.Part268 (cell12404)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086406201900
  | 2 => 0.087367036080
  | 3 => 0.088328845265
  | 4 => 0.089293685075
  | 5 => 0.090264018123
  | 6 => 0.091242771294
  | 7 => 0.092233397833
  | 8 => 0.093239944209
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12404 12404 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12404 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12404

/-! Actual upper energy certificates on all 43 source endpoints at 12404. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12404)
open BstLean.Part268 (cell12404)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12404 (gMinus 12404) (1 - (cell12404 i).lower) ≤ 1 ∧
    energyUpper 12404 (gMinus 12404) (BstLean.Part211.gPlus 12404)
      (finiteEnergy 12404 12404 0.011) (1 - (cell12404 i).lower) ≤
      (cell12404 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨10,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨11,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨12,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨13,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨14,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨15,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨16,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨17,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨18,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨19,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨20,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨21,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨22,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨23,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨24,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨25,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨26,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨27,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨28,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨29,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨30,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨31,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨32,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨33,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨34,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨35,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨36,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨37,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨38,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨39,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨40,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨41,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨42,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨43,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨44,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨45,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨46,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨47,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨48,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨49,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨50,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨51,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12404) (by norm_num)
        (q := 1 - (cell12404 ⟨52,by decide⟩).lower)
        (by norm_num [cell12404]) (by norm_num [cell12404])
      exact ⟨E.1,E.2.trans (by norm_num [cell12404])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12404

/-! Source-cell containment and simple scalar guards at 12404. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12404)
open BstLean.Part268 (cell12404)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12404 ⟨10,by decide⟩).lower ∧ (cell12404 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12404 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12404 ⟨11,by decide⟩).lower ∧ (cell12404 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12404 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12404 ⟨12,by decide⟩).lower ∧ (cell12404 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12404 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12404 ⟨13,by decide⟩).lower ∧ (cell12404 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12404 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12404 ⟨14,by decide⟩).lower ∧ (cell12404 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12404 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12404 ⟨15,by decide⟩).lower ∧ (cell12404 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12404 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12404 ⟨16,by decide⟩).lower ∧ (cell12404 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12404 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12404 ⟨17,by decide⟩).lower ∧ (cell12404 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12404 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12404 ⟨18,by decide⟩).lower ∧ (cell12404 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12404 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12404 ⟨19,by decide⟩).lower ∧ (cell12404 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12404 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12404 ⟨20,by decide⟩).lower ∧ (cell12404 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12404 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12404 ⟨21,by decide⟩).lower ∧ (cell12404 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12404 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12404 ⟨22,by decide⟩).lower ∧ (cell12404 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12404 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12404 ⟨23,by decide⟩).lower ∧ (cell12404 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12404 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12404 ⟨24,by decide⟩).lower ∧ (cell12404 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12404 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12404 ⟨25,by decide⟩).lower ∧ (cell12404 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12404 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12404 ⟨26,by decide⟩).lower ∧ (cell12404 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12404 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12404 ⟨27,by decide⟩).lower ∧ (cell12404 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12404 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12404 ⟨28,by decide⟩).lower ∧ (cell12404 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12404 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12404 ⟨29,by decide⟩).lower ∧ (cell12404 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12404 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12404 ⟨30,by decide⟩).lower ∧ (cell12404 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12404 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12404 ⟨31,by decide⟩).lower ∧ (cell12404 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12404 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12404 ⟨32,by decide⟩).lower ∧ (cell12404 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12404 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12404 ⟨33,by decide⟩).lower ∧ (cell12404 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12404 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12404 ⟨34,by decide⟩).lower ∧ (cell12404 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12404 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12404 ⟨35,by decide⟩).lower ∧ (cell12404 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12404 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12404 ⟨36,by decide⟩).lower ∧ (cell12404 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12404 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12404 ⟨37,by decide⟩).lower ∧ (cell12404 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12404 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12404 ⟨38,by decide⟩).lower ∧ (cell12404 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12404 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12404 ⟨39,by decide⟩).lower ∧ (cell12404 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12404 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12404 ⟨40,by decide⟩).lower ∧ (cell12404 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12404 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12404 ⟨41,by decide⟩).lower ∧ (cell12404 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12404 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12404 ⟨42,by decide⟩).lower ∧ (cell12404 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12404 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12404 ⟨43,by decide⟩).lower ∧ (cell12404 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12404 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12404 ⟨44,by decide⟩).lower ∧ (cell12404 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12404 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12404 ⟨45,by decide⟩).lower ∧ (cell12404 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12404 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12404 ⟨46,by decide⟩).lower ∧ (cell12404 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12404 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12404 ⟨47,by decide⟩).lower ∧ (cell12404 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12404 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12404 ⟨48,by decide⟩).lower ∧ (cell12404 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12404 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12404 ⟨49,by decide⟩).lower ∧ (cell12404 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12404 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12404 ⟨50,by decide⟩).lower ∧ (cell12404 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12404 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12404 ⟨51,by decide⟩).lower ∧ (cell12404 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12404 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12404 ⟨52,by decide⟩).lower ∧ (cell12404 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12404 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12404 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12404 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12404,cell12404,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12404 i).lower ∧
    (cell12404 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12404 i).upper ≤ (0.532 : ℝ) ∧
    (cell12404 i).centre ≤ (0.1 : ℝ) ∧ (cell12404 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12404 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12404 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12404

/-! The local source numeric instances at 12404 have no network premises. -/
namespace BstLean.Part269.N12404
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12404)
open BstLean.Part268 (cell12404)

noncomputable def sourceNumerics12404 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12404 (cell12404 i)
      scalarRow12404.M scalarRow12404.H scalarRow12404.xi := by
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
    energy_allowance := scalarRow12404.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12404]
    centre_nonneg := (scalarRow12404.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12404])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12404
/-! Actual 12405 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12405 ≤ (1.036236271071 : ℝ) := by
  have hr : (111.377735656638 : ℝ) ≤ √(12405 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.377735656638 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12405 12405 (11 / 1000) ≤
    (0.008582389567 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12405) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.377735656638 : ℝ) ≤ √(12405 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12405)
  have hdiv : K / √(12405 : ℝ) ≤ K / 111.377735656638 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.377735656638 ≤ (0.008582389567 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12405.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12405 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12405 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12405 := gPlus_lower 12405
end BstLean.Part269.N12405

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12405
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036236271070 : ℝ) ≤ wn 12405 := by
  have hn : √(12405 : ℝ) ≤ 111.377735656639 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12405 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.377735656639 ≤ 2 / √(12405 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257977097 : ℝ) ≤ rhoBar 12405 BstLean.Part154.csC ∧
    rhoBar 12405 BstLean.Part154.csC ≤ 0.000257977497 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036236271070 : ℝ) / (1.295212 * 12405) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036236271071 : ℝ) / (1.29521 * 12405) := by gcongr
      _ ≤ (0.000257977497 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12405 BstLean.Part154.csC) ≤ 0.001031976541 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12405 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) ≤ 0.000197045174 ∧
    cc1 (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) ≤ 0.000125381107 ∧
    cc2 (rhoBar 12405 BstLean.Part154.csC) ≤ 0.000072784638 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12405 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12405 BstLean.Part154.csC * nuR (rhoBar 12405 BstLean.Part154.csC)) ≤ 0.000515971632 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257977497 : ℝ) * 0.001031976541 := by gcongr
      _ ≤ (0.000515971632 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12405 BstLean.Part154.csC) * nuR (rhoBar 12405 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031976541 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12405 BstLean.Part154.csC) * rhoBar 12405 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257977497 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257977497 / 2 + 0.399 * 0.001031976541 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197045174 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515971632 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125381107 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257977497 / 1.414213562 := by gcongr
      _ ≤ (0.000072784638 : ℝ) := by norm_num

end BstLean.Part269.N12405

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12405
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) ≤ 1.67674E-7 := by
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12405 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12405 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197045174 : ℝ) ^ 2 + 0.000125381107 ^ 2 + 3 * 0.000072784638 ^ 2 +
        2 * 0.797885 * 0.000197045174 * 0.000125381107 + 2 * 0.000197045174 * 0.000072784638 +
        4 * 0.797885 * 0.000125381107 * 0.000072784638 := by gcongr
    _ ≤ (1.67674E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12405 BstLean.Part154.csC Θ ≤ 0.002694035751 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12405 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12405 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036236271071 * 1.67674E-7 / (0.000257977097 : ℝ) := by gcongr
    _ ≤ 0.002694035751 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12405 BstLean.Part154.csC Θ ≤ 0.002990414680 + 0.000680739293 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12405 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036236271071 : ℝ) * ((2 * Θ * 0.000257977497 +
        (6863 / 10000) * 0.000257977497 * 12405 * 0.001031976541) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002990414680 + 0.000680739293 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12405 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12405 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12405 0.011 Θ ∧ gammaRatio 12405 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12405 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036236271071 : ℝ) * 0.525 / ((1 - 0.011) * 12405) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12405 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12405 0.011 Θ) :=
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
    badAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12405 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12405 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12405 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12405 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12405 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12405 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12405 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12405 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12405 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12405 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036236271071 : ℝ) * 12405 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004090414680 + 0.003374775044 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12405

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12405
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12405 BstLean.Part154.csC) (piBar (rhoBar 12405 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12405 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12405 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12405 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12405 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12405 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12405 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12405 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12405 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12405 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053111510565 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12405) ≤ 0.010722408514 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12405 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036236271071)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010722408514 + 2 * 0.737676 / 12405) := by gcongr
    _ ≤ (0.053111510565 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12405 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12405

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12405
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489910261 : ℝ) ≤ plow 12405 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12405) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368771579)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414368770) : eMP 12405 0.011 xi bn ≤ 0.001217287082 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12405 : ℝ) * (1 - 0.011))) ≤ 0.000601810499 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414368770 / (12405 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601810499 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601810499 : ℝ) + 3.141593 * 0.053368771579 / (12405 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217287082 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368771579)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414368770) : PiBarMP 12405 12 0.011 xi bn ≤ 0.163178694160 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12405 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037608094475 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.763464192846 : ℝ) ≤ √((12405 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.377735656638 : ℝ) ≤ √(12405 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12405) ≤ 0.125091502181 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037608094475 + 0.053368771579 * 1.772454 / (2 * (110.763464192846 : ℝ))) * (1 + 0.001217287082) +
        8 / (12405 * 111.377735656638) + 0.125091502181 := by gcongr
    _ ≤ (0.163178694160 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368771579)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414368770) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284128331553) :
    parallelOracle 12405 0.011 xi bn cd ≤ 0.164196638617 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12405 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12405 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489910261 : ℝ) ≤ plow 12405 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.377735656638 : ℝ) ≤ √(12405 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284128331553 : ℝ) / (2 * 0.560489910261 * 111.377735656638)) * 0.163178694160 +
        0.284128331553 ^ 2 / (2 * 0.560489910261 * 111.377735656638) := by gcongr
    _ ≤ (0.164196638617 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368771579) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414368770)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284128331553) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12405 12405 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489910261 : ℝ) ≤ plow 12405 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.377735656638 : ℝ) ≤ √(12405 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12405 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12405 Θ 1.22 ≤ 0.011906333813 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.377735656638 := by gcongr <;> linarith
      _ ≤ (0.011906333813 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12405 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12405 12405 0.011 ≤ 0.008582389567 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12405 12405 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12405 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12405 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12405 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12405 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164196638617 + 0.011906333813 + (0.008582389567 : ℝ) *
        (1 + 2 * (0.284128331553 + 0.011906333813) / (0.560489910261 * 111.377735656638))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12405]

end BstLean.Part269.N12405

/-! The original eight local profiles supply actual 12405 moment certificates. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12405 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053368771579 ∧
    0 ≤ bN 12405 BstLean.Part154.csC (groupTheta g) ∧ bN 12405 BstLean.Part154.csC (groupTheta g) ≤ 0.001414368770 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12405 12405 0.011
      (momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12405 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12405 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12405 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231016820988 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12405 0.011
      (momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12405 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12405
/-! The actual computed-centre upper energy formula at 12405. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12405

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12405)
open BstLean.Part268 (cell12405)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086402910620
  | 2 => 0.087363675182
  | 3 => 0.088325403178
  | 4 => 0.089290147681
  | 5 => 0.090260368328
  | 6 => 0.091238988546
  | 7 => 0.092229457597
  | 8 => 0.093235817379
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12405 12405 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12405 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12405

/-! Actual upper energy certificates on all 43 source endpoints at 12405. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12405)
open BstLean.Part268 (cell12405)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12405 (gMinus 12405) (1 - (cell12405 i).lower) ≤ 1 ∧
    energyUpper 12405 (gMinus 12405) (BstLean.Part211.gPlus 12405)
      (finiteEnergy 12405 12405 0.011) (1 - (cell12405 i).lower) ≤
      (cell12405 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨10,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨11,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨12,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨13,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨14,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨15,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨16,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨17,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨18,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨19,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨20,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨21,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨22,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨23,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨24,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨25,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨26,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨27,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨28,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨29,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨30,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨31,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨32,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨33,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨34,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨35,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨36,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨37,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨38,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨39,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨40,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨41,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨42,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨43,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨44,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨45,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨46,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨47,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨48,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨49,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨50,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨51,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12405) (by norm_num)
        (q := 1 - (cell12405 ⟨52,by decide⟩).lower)
        (by norm_num [cell12405]) (by norm_num [cell12405])
      exact ⟨E.1,E.2.trans (by norm_num [cell12405])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12405

/-! Source-cell containment and simple scalar guards at 12405. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12405)
open BstLean.Part268 (cell12405)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12405 ⟨10,by decide⟩).lower ∧ (cell12405 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12405 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12405 ⟨11,by decide⟩).lower ∧ (cell12405 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12405 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12405 ⟨12,by decide⟩).lower ∧ (cell12405 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12405 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12405 ⟨13,by decide⟩).lower ∧ (cell12405 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12405 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12405 ⟨14,by decide⟩).lower ∧ (cell12405 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12405 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12405 ⟨15,by decide⟩).lower ∧ (cell12405 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12405 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12405 ⟨16,by decide⟩).lower ∧ (cell12405 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12405 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12405 ⟨17,by decide⟩).lower ∧ (cell12405 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12405 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12405 ⟨18,by decide⟩).lower ∧ (cell12405 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12405 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12405 ⟨19,by decide⟩).lower ∧ (cell12405 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12405 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12405 ⟨20,by decide⟩).lower ∧ (cell12405 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12405 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12405 ⟨21,by decide⟩).lower ∧ (cell12405 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12405 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12405 ⟨22,by decide⟩).lower ∧ (cell12405 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12405 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12405 ⟨23,by decide⟩).lower ∧ (cell12405 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12405 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12405 ⟨24,by decide⟩).lower ∧ (cell12405 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12405 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12405 ⟨25,by decide⟩).lower ∧ (cell12405 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12405 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12405 ⟨26,by decide⟩).lower ∧ (cell12405 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12405 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12405 ⟨27,by decide⟩).lower ∧ (cell12405 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12405 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12405 ⟨28,by decide⟩).lower ∧ (cell12405 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12405 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12405 ⟨29,by decide⟩).lower ∧ (cell12405 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12405 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12405 ⟨30,by decide⟩).lower ∧ (cell12405 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12405 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12405 ⟨31,by decide⟩).lower ∧ (cell12405 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12405 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12405 ⟨32,by decide⟩).lower ∧ (cell12405 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12405 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12405 ⟨33,by decide⟩).lower ∧ (cell12405 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12405 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12405 ⟨34,by decide⟩).lower ∧ (cell12405 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12405 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12405 ⟨35,by decide⟩).lower ∧ (cell12405 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12405 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12405 ⟨36,by decide⟩).lower ∧ (cell12405 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12405 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12405 ⟨37,by decide⟩).lower ∧ (cell12405 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12405 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12405 ⟨38,by decide⟩).lower ∧ (cell12405 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12405 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12405 ⟨39,by decide⟩).lower ∧ (cell12405 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12405 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12405 ⟨40,by decide⟩).lower ∧ (cell12405 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12405 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12405 ⟨41,by decide⟩).lower ∧ (cell12405 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12405 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12405 ⟨42,by decide⟩).lower ∧ (cell12405 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12405 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12405 ⟨43,by decide⟩).lower ∧ (cell12405 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12405 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12405 ⟨44,by decide⟩).lower ∧ (cell12405 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12405 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12405 ⟨45,by decide⟩).lower ∧ (cell12405 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12405 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12405 ⟨46,by decide⟩).lower ∧ (cell12405 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12405 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12405 ⟨47,by decide⟩).lower ∧ (cell12405 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12405 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12405 ⟨48,by decide⟩).lower ∧ (cell12405 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12405 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12405 ⟨49,by decide⟩).lower ∧ (cell12405 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12405 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12405 ⟨50,by decide⟩).lower ∧ (cell12405 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12405 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12405 ⟨51,by decide⟩).lower ∧ (cell12405 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12405 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12405 ⟨52,by decide⟩).lower ∧ (cell12405 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12405 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12405 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12405 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12405,cell12405,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12405 i).lower ∧
    (cell12405 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12405 i).upper ≤ (0.532 : ℝ) ∧
    (cell12405 i).centre ≤ (0.1 : ℝ) ∧ (cell12405 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12405 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12405 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12405

/-! The local source numeric instances at 12405 have no network premises. -/
namespace BstLean.Part269.N12405
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12405)
open BstLean.Part268 (cell12405)

noncomputable def sourceNumerics12405 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12405 (cell12405 i)
      scalarRow12405.M scalarRow12405.H scalarRow12405.xi := by
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
    energy_allowance := scalarRow12405.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12405]
    centre_nonneg := (scalarRow12405.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12405])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12405
/-! Actual 12406 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12406 ≤ (1.036234797613 : ℝ) := by
  have hr : (111.382224793725 : ℝ) ≤ √(12406 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.382224793725 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12406 12406 (11 / 1000) ≤
    (0.008582043661 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12406) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.382224793725 : ℝ) ≤ √(12406 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12406)
  have hdiv : K / √(12406 : ℝ) ≤ K / 111.382224793725 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.382224793725 ≤ (0.008582043661 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12406.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12406 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12406 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12406 := gPlus_lower 12406
end BstLean.Part269.N12406

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12406
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036234797612 : ℝ) ≤ wn 12406 := by
  have hn : √(12406 : ℝ) ≤ 111.382224793726 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12406 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.382224793726 ≤ 2 / √(12406 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257955936 : ℝ) ≤ rhoBar 12406 BstLean.Part154.csC ∧
    rhoBar 12406 BstLean.Part154.csC ≤ 0.000257956335 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036234797612 : ℝ) / (1.295212 * 12406) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036234797613 : ℝ) / (1.29521 * 12406) := by gcongr
      _ ≤ (0.000257956335 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12406 BstLean.Part154.csC) ≤ 0.001031891882 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12406 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) ≤ 0.000197029010 ∧
    cc1 (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) ≤ 0.000125370822 ∧
    cc2 (rhoBar 12406 BstLean.Part154.csC) ≤ 0.000072778667 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12406 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12406 BstLean.Part154.csC * nuR (rhoBar 12406 BstLean.Part154.csC)) ≤ 0.000515929306 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257956335 : ℝ) * 0.001031891882 := by gcongr
      _ ≤ (0.000515929306 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12406 BstLean.Part154.csC) * nuR (rhoBar 12406 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031891882 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12406 BstLean.Part154.csC) * rhoBar 12406 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257956335 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257956335 / 2 + 0.399 * 0.001031891882 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197029010 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515929306 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125370822 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257956335 / 1.414213562 := by gcongr
      _ ≤ (0.000072778667 : ℝ) := by norm_num

end BstLean.Part269.N12406

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12406
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) ≤ 1.67647E-7 := by
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12406 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12406 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197029010 : ℝ) ^ 2 + 0.000125370822 ^ 2 + 3 * 0.000072778667 ^ 2 +
        2 * 0.797885 * 0.000197029010 * 0.000125370822 + 2 * 0.000197029010 * 0.000072778667 +
        4 * 0.797885 * 0.000125370822 * 0.000072778667 := by gcongr
    _ ≤ (1.67647E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12406 BstLean.Part154.csC Θ ≤ 0.002693819074 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12406 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12406 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036234797613 * 1.67647E-7 / (0.000257955936 : ℝ) := by gcongr
    _ ≤ 0.002693819074 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12406 BstLean.Part154.csC Θ ≤ 0.002990160848 + 0.000680682484 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12406 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036234797613 : ℝ) * ((2 * Θ * 0.000257956335 +
        (6863 / 10000) * 0.000257956335 * 12406 * 0.001031891882) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002990160848 + 0.000680682484 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12406 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12406 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12406 0.011 Θ ∧ gammaRatio 12406 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12406 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036234797613 : ℝ) * 0.525 / ((1 - 0.011) * 12406) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12406 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12406 0.011 Θ) :=
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
    badAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12406 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12406 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12406 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12406 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12406 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12406 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12406 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12406 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12406 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12406 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036234797613 : ℝ) * 12406 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004090160848 + 0.003374501558 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12406

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12406
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12406 BstLean.Part154.csC) (piBar (rhoBar 12406 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12406 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12406 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12406 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12406 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12406 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12406 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12406 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12406 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12406 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053109346486 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12406) ≤ 0.010721976360 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12406 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036234797613)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010721976360 + 2 * 0.737676 / 12406) := by gcongr
    _ ≤ (0.053109346486 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12406 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12406

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12406
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489957657 : ℝ) ≤ plow 12406 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12406) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368374166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414255014) : eMP 12406 0.011 xi bn ≤ 0.001217188965 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12406 : ℝ) * (1 - 0.011))) ≤ 0.000601762042 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414255014 / (12406 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601762042 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601762042 : ℝ) + 3.141593 * 0.053368374166 / (12406 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217188965 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368374166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414255014) : PiBarMP 12406 12 0.011 xi bn ≤ 0.163172113381 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12406 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037606582057 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.767928571405 : ℝ) ≤ √((12406 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.382224793725 : ℝ) ≤ √(12406 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12406) ≤ 0.125086460507 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037606582057 + 0.053368374166 * 1.772454 / (2 * (110.767928571405 : ℝ))) * (1 + 0.001217188965) +
        8 / (12406 * 111.382224793725) + 0.125086460507 := by gcongr
    _ ≤ (0.163172113381 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368374166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414255014) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284125307333) :
    parallelOracle 12406 0.011 xi bn cd ≤ 0.164189984033 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12406 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12406 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489957657 : ℝ) ≤ plow 12406 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.382224793725 : ℝ) ≤ √(12406 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284125307333 : ℝ) / (2 * 0.560489957657 * 111.382224793725)) * 0.163172113381 +
        0.284125307333 ^ 2 / (2 * 0.560489957657 * 111.382224793725) := by gcongr
    _ ≤ (0.164189984033 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053368374166) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414255014)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284125307333) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12406 12406 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489957657 : ℝ) ≤ plow 12406 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.382224793725 : ℝ) ≤ √(12406 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12406 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12406 Θ 1.22 ≤ 0.011905853941 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.382224793725 := by gcongr <;> linarith
      _ ≤ (0.011905853941 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12406 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12406 12406 0.011 ≤ 0.008582043661 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12406 12406 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12406 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12406 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12406 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12406 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164189984033 + 0.011905853941 + (0.008582043661 : ℝ) *
        (1 + 2 * (0.284125307333 + 0.011905853941) / (0.560489957657 * 111.382224793725))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12406]

end BstLean.Part269.N12406

/-! The original eight local profiles supply actual 12406 moment certificates. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12406 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053368374166 ∧
    0 ≤ bN 12406 BstLean.Part154.csC (groupTheta g) ∧ bN 12406 BstLean.Part154.csC (groupTheta g) ≤ 0.001414255014 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12406 12406 0.011
      (momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12406 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12406 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12406 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231015960847 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12406 0.011
      (momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12406 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12406
/-! The actual computed-centre upper energy formula at 12406. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12406

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12406)
open BstLean.Part268 (cell12406)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086399620818
  | 2 => 0.087360315827
  | 3 => 0.088321962716
  | 4 => 0.089286612011
  | 5 => 0.090256720376
  | 6 => 0.091235207789
  | 7 => 0.092225519527
  | 8 => 0.093231692924
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12406 12406 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12406 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12406

/-! Actual upper energy certificates on all 43 source endpoints at 12406. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12406)
open BstLean.Part268 (cell12406)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12406 (gMinus 12406) (1 - (cell12406 i).lower) ≤ 1 ∧
    energyUpper 12406 (gMinus 12406) (BstLean.Part211.gPlus 12406)
      (finiteEnergy 12406 12406 0.011) (1 - (cell12406 i).lower) ≤
      (cell12406 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨10,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨11,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨12,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨13,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨14,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨15,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨16,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨17,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨18,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨19,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨20,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨21,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨22,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨23,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨24,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨25,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨26,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨27,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨28,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨29,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨30,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨31,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨32,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨33,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨34,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨35,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨36,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨37,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨38,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨39,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨40,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨41,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨42,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨43,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨44,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨45,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨46,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨47,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨48,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨49,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨50,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨51,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12406) (by norm_num)
        (q := 1 - (cell12406 ⟨52,by decide⟩).lower)
        (by norm_num [cell12406]) (by norm_num [cell12406])
      exact ⟨E.1,E.2.trans (by norm_num [cell12406])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12406

/-! Source-cell containment and simple scalar guards at 12406. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12406)
open BstLean.Part268 (cell12406)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12406 ⟨10,by decide⟩).lower ∧ (cell12406 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12406 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12406 ⟨11,by decide⟩).lower ∧ (cell12406 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12406 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12406 ⟨12,by decide⟩).lower ∧ (cell12406 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12406 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12406 ⟨13,by decide⟩).lower ∧ (cell12406 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12406 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12406 ⟨14,by decide⟩).lower ∧ (cell12406 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12406 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12406 ⟨15,by decide⟩).lower ∧ (cell12406 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12406 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12406 ⟨16,by decide⟩).lower ∧ (cell12406 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12406 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12406 ⟨17,by decide⟩).lower ∧ (cell12406 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12406 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12406 ⟨18,by decide⟩).lower ∧ (cell12406 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12406 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12406 ⟨19,by decide⟩).lower ∧ (cell12406 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12406 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12406 ⟨20,by decide⟩).lower ∧ (cell12406 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12406 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12406 ⟨21,by decide⟩).lower ∧ (cell12406 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12406 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12406 ⟨22,by decide⟩).lower ∧ (cell12406 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12406 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12406 ⟨23,by decide⟩).lower ∧ (cell12406 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12406 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12406 ⟨24,by decide⟩).lower ∧ (cell12406 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12406 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12406 ⟨25,by decide⟩).lower ∧ (cell12406 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12406 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12406 ⟨26,by decide⟩).lower ∧ (cell12406 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12406 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12406 ⟨27,by decide⟩).lower ∧ (cell12406 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12406 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12406 ⟨28,by decide⟩).lower ∧ (cell12406 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12406 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12406 ⟨29,by decide⟩).lower ∧ (cell12406 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12406 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12406 ⟨30,by decide⟩).lower ∧ (cell12406 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12406 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12406 ⟨31,by decide⟩).lower ∧ (cell12406 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12406 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12406 ⟨32,by decide⟩).lower ∧ (cell12406 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12406 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12406 ⟨33,by decide⟩).lower ∧ (cell12406 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12406 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12406 ⟨34,by decide⟩).lower ∧ (cell12406 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12406 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12406 ⟨35,by decide⟩).lower ∧ (cell12406 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12406 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12406 ⟨36,by decide⟩).lower ∧ (cell12406 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12406 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12406 ⟨37,by decide⟩).lower ∧ (cell12406 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12406 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12406 ⟨38,by decide⟩).lower ∧ (cell12406 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12406 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12406 ⟨39,by decide⟩).lower ∧ (cell12406 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12406 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12406 ⟨40,by decide⟩).lower ∧ (cell12406 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12406 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12406 ⟨41,by decide⟩).lower ∧ (cell12406 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12406 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12406 ⟨42,by decide⟩).lower ∧ (cell12406 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12406 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12406 ⟨43,by decide⟩).lower ∧ (cell12406 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12406 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12406 ⟨44,by decide⟩).lower ∧ (cell12406 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12406 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12406 ⟨45,by decide⟩).lower ∧ (cell12406 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12406 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12406 ⟨46,by decide⟩).lower ∧ (cell12406 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12406 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12406 ⟨47,by decide⟩).lower ∧ (cell12406 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12406 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12406 ⟨48,by decide⟩).lower ∧ (cell12406 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12406 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12406 ⟨49,by decide⟩).lower ∧ (cell12406 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12406 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12406 ⟨50,by decide⟩).lower ∧ (cell12406 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12406 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12406 ⟨51,by decide⟩).lower ∧ (cell12406 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12406 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12406 ⟨52,by decide⟩).lower ∧ (cell12406 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12406 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12406 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12406 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12406,cell12406,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12406 i).lower ∧
    (cell12406 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12406 i).upper ≤ (0.532 : ℝ) ∧
    (cell12406 i).centre ≤ (0.1 : ℝ) ∧ (cell12406 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12406 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12406 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12406

/-! The local source numeric instances at 12406 have no network premises. -/
namespace BstLean.Part269.N12406
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12406)
open BstLean.Part268 (cell12406)

noncomputable def sourceNumerics12406 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12406 (cell12406 i)
      scalarRow12406.M scalarRow12406.H scalarRow12406.xi := by
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
    energy_allowance := scalarRow12406.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12406]
    centre_nonneg := (scalarRow12406.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12406])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12406
/-! Actual 12407 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12407 ≤ (1.036233324334 : ℝ) := by
  have hr : (111.386713749890 : ℝ) ≤ √(12407 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.386713749890 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12407 12407 (11 / 1000) ≤
    (0.008581697796 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12407) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.386713749890 : ℝ) ≤ √(12407 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12407)
  have hdiv : K / √(12407 : ℝ) ≤ K / 111.386713749890 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.386713749890 ≤ (0.008581697796 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12407.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12407 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12407 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12407 := gPlus_lower 12407
end BstLean.Part269.N12407

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12407
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036233324333 : ℝ) ≤ wn 12407 := by
  have hn : √(12407 : ℝ) ≤ 111.386713749891 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12407 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.386713749891 ≤ 2 / √(12407 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257934778 : ℝ) ≤ rhoBar 12407 BstLean.Part154.csC ∧
    rhoBar 12407 BstLean.Part154.csC ≤ 0.000257935178 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036233324333 : ℝ) / (1.295212 * 12407) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036233324334 : ℝ) / (1.29521 * 12407) := by gcongr
      _ ≤ (0.000257935178 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12407 BstLean.Part154.csC) ≤ 0.001031807243 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12407 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) ≤ 0.000197012849 ∧
    cc1 (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) ≤ 0.000125360539 ∧
    cc2 (rhoBar 12407 BstLean.Part154.csC) ≤ 0.000072772698 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12407 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12407 BstLean.Part154.csC * nuR (rhoBar 12407 BstLean.Part154.csC)) ≤ 0.000515886989 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257935178 : ℝ) * 0.001031807243 := by gcongr
      _ ≤ (0.000515886989 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12407 BstLean.Part154.csC) * nuR (rhoBar 12407 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031807243 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12407 BstLean.Part154.csC) * rhoBar 12407 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257935178 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257935178 / 2 + 0.399 * 0.001031807243 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197012849 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515886989 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125360539 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257935178 / 1.414213562 := by gcongr
      _ ≤ (0.000072772698 : ℝ) := by norm_num

end BstLean.Part269.N12407

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12407
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) ≤ 1.67619E-7 := by
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12407 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12407 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197012849 : ℝ) ^ 2 + 0.000125360539 ^ 2 + 3 * 0.000072772698 ^ 2 +
        2 * 0.797885 * 0.000197012849 * 0.000125360539 + 2 * 0.000197012849 * 0.000072772698 +
        4 * 0.797885 * 0.000125360539 * 0.000072772698 := by gcongr
    _ ≤ (1.67619E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12407 BstLean.Part154.csC Θ ≤ 0.002693586262 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12407 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12407 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036233324334 * 1.67619E-7 / (0.000257934778 : ℝ) := by gcongr
    _ ≤ 0.002693586262 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12407 BstLean.Part154.csC Θ ≤ 0.002989907094 + 0.000680625688 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12407 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036233324334 : ℝ) * ((2 * Θ * 0.000257935178 +
        (6863 / 10000) * 0.000257935178 * 12407 * 0.001031807243) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002989907094 + 0.000680625688 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12407 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12407 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12407 0.011 Θ ∧ gammaRatio 12407 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12407 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036233324334 : ℝ) * 0.525 / ((1 - 0.011) * 12407) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12407 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12407 0.011 Θ) :=
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
    badAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12407 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12407 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12407 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12407 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12407 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12407 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12407 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12407 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12407 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12407 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036233324334 : ℝ) * 12407 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004089907094 + 0.003374211950 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12407

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12407
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12407 BstLean.Part154.csC) (piBar (rhoBar 12407 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12407 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12407 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12407 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12407 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12407 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12407 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12407 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12407 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12407 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053107182665 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12407) ≤ 0.010721544257 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12407 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036233324334)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010721544257 + 2 * 0.737676 / 12407) := by gcongr
    _ ≤ (0.053107182665 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12407 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12407

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12407
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490005045 : ℝ) ≤ plow 12407 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12407) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367968368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414132788) : eMP 12407 0.011 xi bn ≤ 0.001217087251 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12407 : ℝ) * (1 - 0.011))) ≤ 0.000601711788 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414132788 / (12407 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601711788 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601711788 : ℝ) + 3.141593 * 0.053367968368 / (12407 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217087251 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367968368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414132788) : PiBarMP 12407 12 0.011 xi bn ≤ 0.163165420194 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12407 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037604956961 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.772392770039 : ℝ) ≤ √((12407 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.386713749890 : ℝ) ≤ √(12407 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12407) ≤ 0.125081419442 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037604956961 + 0.053367968368 * 1.772454 / (2 * (110.772392770039 : ℝ))) * (1 + 0.001217087251) +
        8 / (12407 * 111.386713749890) + 0.125081419442 := by gcongr
    _ ≤ (0.163165420194 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367968368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414132788) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284122265221) :
    parallelOracle 12407 0.011 xi bn cd ≤ 0.164183216689 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12407 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12407 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490005045 : ℝ) ≤ plow 12407 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.386713749890 : ℝ) ≤ √(12407 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284122265221 : ℝ) / (2 * 0.560490005045 * 111.386713749890)) * 0.163165420194 +
        0.284122265221 ^ 2 / (2 * 0.560490005045 * 111.386713749890) := by gcongr
    _ ≤ (0.164183216689 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367968368) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414132788)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284122265221) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12407 12407 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490005045 : ℝ) ≤ plow 12407 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.386713749890 : ℝ) ≤ √(12407 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12407 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12407 Θ 1.22 ≤ 0.011905374128 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.386713749890 := by gcongr <;> linarith
      _ ≤ (0.011905374128 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12407 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12407 12407 0.011 ≤ 0.008581697796 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12407 12407 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12407 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12407 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12407 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12407 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164183216689 + 0.011905374128 + (0.008581697796 : ℝ) *
        (1 + 2 * (0.284122265221 + 0.011905374128) / (0.560490005045 * 111.386713749890))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12407]

end BstLean.Part269.N12407

/-! The original eight local profiles supply actual 12407 moment certificates. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12407 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053367968368 ∧
    0 ≤ bN 12407 BstLean.Part154.csC (groupTheta g) ∧ bN 12407 BstLean.Part154.csC (groupTheta g) ≤ 0.001414132788 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12407 12407 0.011
      (momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12407 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12407 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12407 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231015082556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12407 0.011
      (momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12407 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12407
/-! The actual computed-centre upper energy formula at 12407. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12407

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12407)
open BstLean.Part268 (cell12407)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086396332493
  | 2 => 0.087356958015
  | 3 => 0.088318523876
  | 4 => 0.089283078062
  | 5 => 0.090253074267
  | 6 => 0.091231429019
  | 7 => 0.092221583619
  | 8 => 0.093227570843
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12407 12407 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12407 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12407

/-! Actual upper energy certificates on all 43 source endpoints at 12407. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12407)
open BstLean.Part268 (cell12407)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12407 (gMinus 12407) (1 - (cell12407 i).lower) ≤ 1 ∧
    energyUpper 12407 (gMinus 12407) (BstLean.Part211.gPlus 12407)
      (finiteEnergy 12407 12407 0.011) (1 - (cell12407 i).lower) ≤
      (cell12407 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨10,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨11,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨12,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨13,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨14,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨15,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨16,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨17,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨18,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨19,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨20,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨21,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨22,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨23,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨24,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨25,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨26,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨27,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨28,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨29,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨30,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨31,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨32,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨33,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨34,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨35,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨36,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨37,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨38,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨39,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨40,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨41,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨42,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨43,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨44,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨45,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨46,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨47,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨48,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨49,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨50,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨51,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12407) (by norm_num)
        (q := 1 - (cell12407 ⟨52,by decide⟩).lower)
        (by norm_num [cell12407]) (by norm_num [cell12407])
      exact ⟨E.1,E.2.trans (by norm_num [cell12407])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12407

/-! Source-cell containment and simple scalar guards at 12407. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12407)
open BstLean.Part268 (cell12407)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12407 ⟨10,by decide⟩).lower ∧ (cell12407 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12407 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12407 ⟨11,by decide⟩).lower ∧ (cell12407 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12407 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12407 ⟨12,by decide⟩).lower ∧ (cell12407 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12407 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12407 ⟨13,by decide⟩).lower ∧ (cell12407 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12407 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12407 ⟨14,by decide⟩).lower ∧ (cell12407 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12407 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12407 ⟨15,by decide⟩).lower ∧ (cell12407 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12407 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12407 ⟨16,by decide⟩).lower ∧ (cell12407 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12407 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12407 ⟨17,by decide⟩).lower ∧ (cell12407 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12407 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12407 ⟨18,by decide⟩).lower ∧ (cell12407 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12407 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12407 ⟨19,by decide⟩).lower ∧ (cell12407 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12407 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12407 ⟨20,by decide⟩).lower ∧ (cell12407 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12407 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12407 ⟨21,by decide⟩).lower ∧ (cell12407 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12407 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12407 ⟨22,by decide⟩).lower ∧ (cell12407 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12407 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12407 ⟨23,by decide⟩).lower ∧ (cell12407 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12407 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12407 ⟨24,by decide⟩).lower ∧ (cell12407 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12407 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12407 ⟨25,by decide⟩).lower ∧ (cell12407 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12407 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12407 ⟨26,by decide⟩).lower ∧ (cell12407 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12407 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12407 ⟨27,by decide⟩).lower ∧ (cell12407 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12407 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12407 ⟨28,by decide⟩).lower ∧ (cell12407 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12407 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12407 ⟨29,by decide⟩).lower ∧ (cell12407 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12407 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12407 ⟨30,by decide⟩).lower ∧ (cell12407 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12407 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12407 ⟨31,by decide⟩).lower ∧ (cell12407 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12407 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12407 ⟨32,by decide⟩).lower ∧ (cell12407 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12407 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12407 ⟨33,by decide⟩).lower ∧ (cell12407 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12407 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12407 ⟨34,by decide⟩).lower ∧ (cell12407 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12407 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12407 ⟨35,by decide⟩).lower ∧ (cell12407 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12407 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12407 ⟨36,by decide⟩).lower ∧ (cell12407 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12407 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12407 ⟨37,by decide⟩).lower ∧ (cell12407 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12407 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12407 ⟨38,by decide⟩).lower ∧ (cell12407 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12407 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12407 ⟨39,by decide⟩).lower ∧ (cell12407 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12407 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12407 ⟨40,by decide⟩).lower ∧ (cell12407 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12407 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12407 ⟨41,by decide⟩).lower ∧ (cell12407 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12407 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12407 ⟨42,by decide⟩).lower ∧ (cell12407 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12407 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12407 ⟨43,by decide⟩).lower ∧ (cell12407 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12407 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12407 ⟨44,by decide⟩).lower ∧ (cell12407 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12407 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12407 ⟨45,by decide⟩).lower ∧ (cell12407 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12407 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12407 ⟨46,by decide⟩).lower ∧ (cell12407 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12407 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12407 ⟨47,by decide⟩).lower ∧ (cell12407 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12407 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12407 ⟨48,by decide⟩).lower ∧ (cell12407 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12407 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12407 ⟨49,by decide⟩).lower ∧ (cell12407 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12407 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12407 ⟨50,by decide⟩).lower ∧ (cell12407 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12407 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12407 ⟨51,by decide⟩).lower ∧ (cell12407 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12407 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12407 ⟨52,by decide⟩).lower ∧ (cell12407 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12407 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12407 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12407 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12407,cell12407,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12407 i).lower ∧
    (cell12407 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12407 i).upper ≤ (0.532 : ℝ) ∧
    (cell12407 i).centre ≤ (0.1 : ℝ) ∧ (cell12407 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12407 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12407 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12407

/-! The local source numeric instances at 12407 have no network premises. -/
namespace BstLean.Part269.N12407
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12407)
open BstLean.Part268 (cell12407)

noncomputable def sourceNumerics12407 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12407 (cell12407 i)
      scalarRow12407.M scalarRow12407.H scalarRow12407.xi := by
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
    energy_allowance := scalarRow12407.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12407]
    centre_nonneg := (scalarRow12407.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12407])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12407
/-! Actual 12408 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12408 ≤ (1.036231851234 : ℝ) := by
  have hr : (111.391202525154 : ℝ) ≤ √(12408 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.391202525154 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12408 12408 (11 / 1000) ≤
    (0.008581351973 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12408) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.391202525154 : ℝ) ≤ √(12408 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12408)
  have hdiv : K / √(12408 : ℝ) ≤ K / 111.391202525154 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.391202525154 ≤ (0.008581351973 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12408.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12408 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12408 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12408 := gPlus_lower 12408
end BstLean.Part269.N12408

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12408
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036231851233 : ℝ) ≤ wn 12408 := by
  have hn : √(12408 : ℝ) ≤ 111.391202525155 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12408 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.391202525155 ≤ 2 / √(12408 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257913624 : ℝ) ≤ rhoBar 12408 BstLean.Part154.csC ∧
    rhoBar 12408 BstLean.Part154.csC ≤ 0.000257914023 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036231851233 : ℝ) / (1.295212 * 12408) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036231851234 : ℝ) / (1.29521 * 12408) := by gcongr
      _ ≤ (0.000257914023 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12408 BstLean.Part154.csC) ≤ 0.001031722612 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12408 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) ≤ 0.000196996690 ∧
    cc1 (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) ≤ 0.000125350257 ∧
    cc2 (rhoBar 12408 BstLean.Part154.csC) ≤ 0.000072766730 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12408 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12408 BstLean.Part154.csC * nuR (rhoBar 12408 BstLean.Part154.csC)) ≤ 0.000515844676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257914023 : ℝ) * 0.001031722612 := by gcongr
      _ ≤ (0.000515844676 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12408 BstLean.Part154.csC) * nuR (rhoBar 12408 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031722612 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12408 BstLean.Part154.csC) * rhoBar 12408 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257914023 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257914023 / 2 + 0.399 * 0.001031722612 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196996690 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515844676 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125350257 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257914023 / 1.414213562 := by gcongr
      _ ≤ (0.000072766730 : ℝ) := by norm_num

end BstLean.Part269.N12408

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12408
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) ≤ 1.67592E-7 := by
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12408 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12408 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196996690 : ℝ) ^ 2 + 0.000125350257 ^ 2 + 3 * 0.000072766730 ^ 2 +
        2 * 0.797885 * 0.000196996690 * 0.000125350257 + 2 * 0.000196996690 * 0.000072766730 +
        4 * 0.797885 * 0.000125350257 * 0.000072766730 := by gcongr
    _ ≤ (1.67592E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12408 BstLean.Part154.csC Θ ≤ 0.002693369443 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12408 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12408 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036231851234 * 1.67592E-7 / (0.000257913624 : ℝ) := by gcongr
    _ ≤ 0.002693369443 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12408 BstLean.Part154.csC Θ ≤ 0.002989653349 + 0.000680568898 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12408 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036231851234 : ℝ) * ((2 * Θ * 0.000257914023 +
        (6863 / 10000) * 0.000257914023 * 12408 * 0.001031722612) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002989653349 + 0.000680568898 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12408 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12408 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12408 0.011 Θ ∧ gammaRatio 12408 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12408 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036231851234 : ℝ) * 0.525 / ((1 - 0.011) * 12408) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12408 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12408 0.011 Θ) :=
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
    badAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12408 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12408 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12408 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12408 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12408 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12408 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12408 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12408 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12408 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12408 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036231851234 : ℝ) * 12408 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004089653349 + 0.003373938341 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12408

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12408
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12408 BstLean.Part154.csC) (piBar (rhoBar 12408 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12408 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12408 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12408 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12408 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12408 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12408 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12408 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12408 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12408 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053105019111 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12408) ≤ 0.010721112207 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12408 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036231851234)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010721112207 + 2 * 0.737676 / 12408) := by gcongr
    _ ≤ (0.053105019111 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12408 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12408

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12408
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490052425 : ℝ) ≤ plow 12408 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12408) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367570979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414018958) : eMP 12408 0.011 xi bn ≤ 0.001216989120 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12408 : ℝ) * (1 - 0.011))) ≤ 0.000601663324 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001414018958 / (12408 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601663324 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601663324 : ℝ) + 3.141593 * 0.053367570979 / (12408 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216989120 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367570979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414018958) : PiBarMP 12408 12 0.011 xi bn ≤ 0.163158839527 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12408 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037603443433 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.776856788771 : ℝ) ≤ √((12408 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.391202525154 : ℝ) ≤ √(12408 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12408) ≤ 0.125076378987 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037603443433 + 0.053367570979 * 1.772454 / (2 * (110.776856788771 : ℝ))) * (1 + 0.001216989120) +
        8 / (12408 * 111.391202525154) + 0.125076378987 := by gcongr
    _ ≤ (0.163158839527 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367570979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414018958) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284119241572) :
    parallelOracle 12408 0.011 xi bn cd ≤ 0.164176562237 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12408 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12408 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490052425 : ℝ) ≤ plow 12408 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.391202525154 : ℝ) ≤ √(12408 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284119241572 : ℝ) / (2 * 0.560490052425 * 111.391202525154)) * 0.163158839527 +
        0.284119241572 ^ 2 / (2 * 0.560490052425 * 111.391202525154) := by gcongr
    _ ≤ (0.164176562237 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367570979) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001414018958)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284119241572) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12408 12408 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490052425 : ℝ) ≤ plow 12408 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.391202525154 : ℝ) ≤ √(12408 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12408 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12408 Θ 1.22 ≤ 0.011904894372 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.391202525154 := by gcongr <;> linarith
      _ ≤ (0.011904894372 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12408 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12408 12408 0.011 ≤ 0.008581351973 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12408 12408 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12408 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12408 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12408 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12408 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164176562237 + 0.011904894372 + (0.008581351973 : ℝ) *
        (1 + 2 * (0.284119241572 + 0.011904894372) / (0.560490052425 * 111.391202525154))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12408]

end BstLean.Part269.N12408

/-! The original eight local profiles supply actual 12408 moment certificates. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12408 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053367570979 ∧
    0 ≤ bN 12408 BstLean.Part154.csC (groupTheta g) ∧ bN 12408 BstLean.Part154.csC (groupTheta g) ≤ 0.001414018958 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12408 12408 0.011
      (momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12408 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12408 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12408 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231014222461 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12408 0.011
      (momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12408 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12408
/-! The actual computed-centre upper energy formula at 12408. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12408

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12408)
open BstLean.Part268 (cell12408)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086393045644
  | 2 => 0.087353601743
  | 3 => 0.088315086658
  | 4 => 0.089279545833
  | 5 => 0.090249429997
  | 6 => 0.091227652234
  | 7 => 0.092217649873
  | 8 => 0.093223451133
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12408 12408 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12408 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12408

/-! Actual upper energy certificates on all 43 source endpoints at 12408. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12408)
open BstLean.Part268 (cell12408)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12408 (gMinus 12408) (1 - (cell12408 i).lower) ≤ 1 ∧
    energyUpper 12408 (gMinus 12408) (BstLean.Part211.gPlus 12408)
      (finiteEnergy 12408 12408 0.011) (1 - (cell12408 i).lower) ≤
      (cell12408 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨10,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨11,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨12,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨13,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨14,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨15,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨16,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨17,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨18,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨19,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨20,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨21,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨22,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨23,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨24,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨25,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨26,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨27,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨28,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨29,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨30,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨31,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨32,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨33,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨34,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨35,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨36,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨37,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨38,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨39,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨40,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨41,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨42,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨43,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨44,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨45,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨46,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨47,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨48,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨49,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨50,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨51,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12408) (by norm_num)
        (q := 1 - (cell12408 ⟨52,by decide⟩).lower)
        (by norm_num [cell12408]) (by norm_num [cell12408])
      exact ⟨E.1,E.2.trans (by norm_num [cell12408])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12408

/-! Source-cell containment and simple scalar guards at 12408. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12408)
open BstLean.Part268 (cell12408)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12408 ⟨10,by decide⟩).lower ∧ (cell12408 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12408 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12408 ⟨11,by decide⟩).lower ∧ (cell12408 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12408 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12408 ⟨12,by decide⟩).lower ∧ (cell12408 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12408 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12408 ⟨13,by decide⟩).lower ∧ (cell12408 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12408 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12408 ⟨14,by decide⟩).lower ∧ (cell12408 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12408 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12408 ⟨15,by decide⟩).lower ∧ (cell12408 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12408 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12408 ⟨16,by decide⟩).lower ∧ (cell12408 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12408 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12408 ⟨17,by decide⟩).lower ∧ (cell12408 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12408 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12408 ⟨18,by decide⟩).lower ∧ (cell12408 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12408 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12408 ⟨19,by decide⟩).lower ∧ (cell12408 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12408 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12408 ⟨20,by decide⟩).lower ∧ (cell12408 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12408 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12408 ⟨21,by decide⟩).lower ∧ (cell12408 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12408 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12408 ⟨22,by decide⟩).lower ∧ (cell12408 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12408 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12408 ⟨23,by decide⟩).lower ∧ (cell12408 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12408 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12408 ⟨24,by decide⟩).lower ∧ (cell12408 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12408 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12408 ⟨25,by decide⟩).lower ∧ (cell12408 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12408 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12408 ⟨26,by decide⟩).lower ∧ (cell12408 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12408 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12408 ⟨27,by decide⟩).lower ∧ (cell12408 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12408 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12408 ⟨28,by decide⟩).lower ∧ (cell12408 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12408 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12408 ⟨29,by decide⟩).lower ∧ (cell12408 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12408 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12408 ⟨30,by decide⟩).lower ∧ (cell12408 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12408 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12408 ⟨31,by decide⟩).lower ∧ (cell12408 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12408 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12408 ⟨32,by decide⟩).lower ∧ (cell12408 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12408 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12408 ⟨33,by decide⟩).lower ∧ (cell12408 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12408 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12408 ⟨34,by decide⟩).lower ∧ (cell12408 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12408 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12408 ⟨35,by decide⟩).lower ∧ (cell12408 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12408 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12408 ⟨36,by decide⟩).lower ∧ (cell12408 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12408 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12408 ⟨37,by decide⟩).lower ∧ (cell12408 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12408 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12408 ⟨38,by decide⟩).lower ∧ (cell12408 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12408 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12408 ⟨39,by decide⟩).lower ∧ (cell12408 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12408 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12408 ⟨40,by decide⟩).lower ∧ (cell12408 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12408 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12408 ⟨41,by decide⟩).lower ∧ (cell12408 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12408 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12408 ⟨42,by decide⟩).lower ∧ (cell12408 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12408 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12408 ⟨43,by decide⟩).lower ∧ (cell12408 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12408 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12408 ⟨44,by decide⟩).lower ∧ (cell12408 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12408 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12408 ⟨45,by decide⟩).lower ∧ (cell12408 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12408 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12408 ⟨46,by decide⟩).lower ∧ (cell12408 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12408 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12408 ⟨47,by decide⟩).lower ∧ (cell12408 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12408 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12408 ⟨48,by decide⟩).lower ∧ (cell12408 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12408 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12408 ⟨49,by decide⟩).lower ∧ (cell12408 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12408 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12408 ⟨50,by decide⟩).lower ∧ (cell12408 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12408 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12408 ⟨51,by decide⟩).lower ∧ (cell12408 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12408 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12408 ⟨52,by decide⟩).lower ∧ (cell12408 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12408 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12408 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12408 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12408,cell12408,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12408 i).lower ∧
    (cell12408 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12408 i).upper ≤ (0.532 : ℝ) ∧
    (cell12408 i).centre ≤ (0.1 : ℝ) ∧ (cell12408 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12408 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12408 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12408

/-! The local source numeric instances at 12408 have no network premises. -/
namespace BstLean.Part269.N12408
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12408)
open BstLean.Part268 (cell12408)

noncomputable def sourceNumerics12408 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12408 (cell12408 i)
      scalarRow12408.M scalarRow12408.H scalarRow12408.xi := by
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
    energy_allowance := scalarRow12408.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12408]
    centre_nonneg := (scalarRow12408.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12408])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12408
/-! Actual 12409 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12409 ≤ (1.036230378313 : ℝ) := by
  have hr : (111.395691119540 : ℝ) ≤ √(12409 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.395691119540 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12409 12409 (11 / 1000) ≤
    (0.008581006192 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12409) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.395691119540 : ℝ) ≤ √(12409 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12409)
  have hdiv : K / √(12409 : ℝ) ≤ K / 111.395691119540 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.395691119540 ≤ (0.008581006192 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12409.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12409 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12409 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12409 := gPlus_lower 12409
end BstLean.Part269.N12409

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12409
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036230378312 : ℝ) ≤ wn 12409 := by
  have hn : √(12409 : ℝ) ≤ 111.395691119541 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12409 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.395691119541 ≤ 2 / √(12409 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257892473 : ℝ) ≤ rhoBar 12409 BstLean.Part154.csC ∧
    rhoBar 12409 BstLean.Part154.csC ≤ 0.000257892872 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036230378312 : ℝ) / (1.295212 * 12409) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036230378313 : ℝ) / (1.29521 * 12409) := by gcongr
      _ ≤ (0.000257892872 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12409 BstLean.Part154.csC) ≤ 0.001031637997 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12409 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) ≤ 0.000196980534 ∧
    cc1 (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) ≤ 0.000125339977 ∧
    cc2 (rhoBar 12409 BstLean.Part154.csC) ≤ 0.000072760762 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12409 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12409 BstLean.Part154.csC * nuR (rhoBar 12409 BstLean.Part154.csC)) ≤ 0.000515802371 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257892872 : ℝ) * 0.001031637997 := by gcongr
      _ ≤ (0.000515802371 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12409 BstLean.Part154.csC) * nuR (rhoBar 12409 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031637997 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12409 BstLean.Part154.csC) * rhoBar 12409 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257892872 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257892872 / 2 + 0.399 * 0.001031637997 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196980534 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515802371 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125339977 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257892872 / 1.414213562 := by gcongr
      _ ≤ (0.000072760762 : ℝ) := by norm_num

end BstLean.Part269.N12409

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12409
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) ≤ 1.67564E-7 := by
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12409 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12409 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196980534 : ℝ) ^ 2 + 0.000125339977 ^ 2 + 3 * 0.000072760762 ^ 2 +
        2 * 0.797885 * 0.000196980534 * 0.000125339977 + 2 * 0.000196980534 * 0.000072760762 +
        4 * 0.797885 * 0.000125339977 * 0.000072760762 := by gcongr
    _ ≤ (1.67564E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12409 BstLean.Part154.csC Θ ≤ 0.002693136486 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12409 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12409 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036230378313 * 1.67564E-7 / (0.000257892473 : ℝ) := by gcongr
    _ ≤ 0.002693136486 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12409 BstLean.Part154.csC Θ ≤ 0.002989399660 + 0.000680512119 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12409 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036230378313 : ℝ) * ((2 * Θ * 0.000257892872 +
        (6863 / 10000) * 0.000257892872 * 12409 * 0.001031637997) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002989399660 + 0.000680512119 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12409 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12409 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12409 0.011 Θ ∧ gammaRatio 12409 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12409 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036230378313 : ℝ) * 0.525 / ((1 - 0.011) * 12409) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12409 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12409 0.011 Θ) :=
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
    badAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12409 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12409 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12409 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12409 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12409 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12409 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12409 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12409 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12409 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12409 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036230378313 : ℝ) * 12409 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004089399660 + 0.003373648605 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12409

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12409
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12409 BstLean.Part154.csC) (piBar (rhoBar 12409 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12409 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12409 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12409 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12409 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12409 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12409 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12409 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12409 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12409 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053102855819 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12409) ≤ 0.010720680209 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12409 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036230378313)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010720680209 + 2 * 0.737676 / 12409) := by gcongr
    _ ≤ (0.053102855819 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12409 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12409

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12409
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490099798 : ℝ) ≤ plow 12409 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12409) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367165178)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413896656) : eMP 12409 0.011 xi bn ≤ 0.001216887389 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12409 : ℝ) * (1 - 0.011))) ≤ 0.000601613061 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413896656 / (12409 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601613061 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601613061 : ℝ) + 3.141593 * 0.053367165178 / (12409 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216887389 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367165178)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413896656) : PiBarMP 12409 12 0.011 xi bn ≤ 0.163152146417 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12409 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037601817191 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.781320627622 : ℝ) ≤ √((12409 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.395691119540 : ℝ) ≤ √(12409 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12409) ≤ 0.125071339141 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037601817191 + 0.053367165178 * 1.772454 / (2 * (110.781320627622 : ℝ))) * (1 + 0.001216887389) +
        8 / (12409 * 111.395691119540) + 0.125071339141 := by gcongr
    _ ≤ (0.163152146417 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367165178)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413896656) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284116199975) :
    parallelOracle 12409 0.011 xi bn cd ≤ 0.164169794989 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12409 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12409 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490099798 : ℝ) ≤ plow 12409 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.395691119540 : ℝ) ≤ √(12409 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284116199975 : ℝ) / (2 * 0.560490099798 * 111.395691119540)) * 0.163152146417 +
        0.284116199975 ^ 2 / (2 * 0.560490099798 * 111.395691119540) := by gcongr
    _ ≤ (0.164169794989 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053367165178) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413896656)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284116199975) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12409 12409 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490099798 : ℝ) ≤ plow 12409 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.395691119540 : ℝ) ≤ √(12409 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12409 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12409 Θ 1.22 ≤ 0.011904414675 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.395691119540 := by gcongr <;> linarith
      _ ≤ (0.011904414675 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12409 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12409 12409 0.011 ≤ 0.008581006192 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12409 12409 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12409 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12409 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12409 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12409 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164169794989 + 0.011904414675 + (0.008581006192 : ℝ) *
        (1 + 2 * (0.284116199975 + 0.011904414675) / (0.560490099798 * 111.395691119540))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12409]

end BstLean.Part269.N12409

/-! The original eight local profiles supply actual 12409 moment certificates. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12409 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053367165178 ∧
    0 ≤ bN 12409 BstLean.Part154.csC (groupTheta g) ∧ bN 12409 BstLean.Part154.csC (groupTheta g) ≤ 0.001413896656 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12409 12409 0.011
      (momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12409 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12409 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12409 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231013344156 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12409 0.011
      (momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12409 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12409
/-! The actual computed-centre upper energy formula at 12409. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12409

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12409)
open BstLean.Part268 (cell12409)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086389760268
  | 2 => 0.087350247011
  | 3 => 0.088311651058
  | 4 => 0.089276015321
  | 5 => 0.090245787564
  | 6 => 0.091223877432
  | 7 => 0.092213718285
  | 8 => 0.093219333791
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12409 12409 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12409 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12409

/-! Actual upper energy certificates on all 43 source endpoints at 12409. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12409)
open BstLean.Part268 (cell12409)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12409 (gMinus 12409) (1 - (cell12409 i).lower) ≤ 1 ∧
    energyUpper 12409 (gMinus 12409) (BstLean.Part211.gPlus 12409)
      (finiteEnergy 12409 12409 0.011) (1 - (cell12409 i).lower) ≤
      (cell12409 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨10,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨11,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨12,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨13,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨14,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨15,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨16,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨17,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨18,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨19,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨20,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨21,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨22,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨23,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨24,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨25,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨26,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨27,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨28,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨29,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨30,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨31,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨32,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨33,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨34,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨35,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨36,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨37,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨38,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨39,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨40,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨41,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨42,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨43,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨44,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨45,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨46,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨47,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨48,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨49,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨50,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨51,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12409) (by norm_num)
        (q := 1 - (cell12409 ⟨52,by decide⟩).lower)
        (by norm_num [cell12409]) (by norm_num [cell12409])
      exact ⟨E.1,E.2.trans (by norm_num [cell12409])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12409

/-! Source-cell containment and simple scalar guards at 12409. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12409)
open BstLean.Part268 (cell12409)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12409 ⟨10,by decide⟩).lower ∧ (cell12409 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12409 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12409 ⟨11,by decide⟩).lower ∧ (cell12409 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12409 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12409 ⟨12,by decide⟩).lower ∧ (cell12409 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12409 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12409 ⟨13,by decide⟩).lower ∧ (cell12409 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12409 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12409 ⟨14,by decide⟩).lower ∧ (cell12409 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12409 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12409 ⟨15,by decide⟩).lower ∧ (cell12409 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12409 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12409 ⟨16,by decide⟩).lower ∧ (cell12409 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12409 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12409 ⟨17,by decide⟩).lower ∧ (cell12409 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12409 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12409 ⟨18,by decide⟩).lower ∧ (cell12409 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12409 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12409 ⟨19,by decide⟩).lower ∧ (cell12409 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12409 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12409 ⟨20,by decide⟩).lower ∧ (cell12409 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12409 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12409 ⟨21,by decide⟩).lower ∧ (cell12409 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12409 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12409 ⟨22,by decide⟩).lower ∧ (cell12409 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12409 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12409 ⟨23,by decide⟩).lower ∧ (cell12409 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12409 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12409 ⟨24,by decide⟩).lower ∧ (cell12409 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12409 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12409 ⟨25,by decide⟩).lower ∧ (cell12409 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12409 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12409 ⟨26,by decide⟩).lower ∧ (cell12409 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12409 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12409 ⟨27,by decide⟩).lower ∧ (cell12409 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12409 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12409 ⟨28,by decide⟩).lower ∧ (cell12409 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12409 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12409 ⟨29,by decide⟩).lower ∧ (cell12409 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12409 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12409 ⟨30,by decide⟩).lower ∧ (cell12409 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12409 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12409 ⟨31,by decide⟩).lower ∧ (cell12409 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12409 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12409 ⟨32,by decide⟩).lower ∧ (cell12409 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12409 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12409 ⟨33,by decide⟩).lower ∧ (cell12409 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12409 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12409 ⟨34,by decide⟩).lower ∧ (cell12409 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12409 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12409 ⟨35,by decide⟩).lower ∧ (cell12409 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12409 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12409 ⟨36,by decide⟩).lower ∧ (cell12409 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12409 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12409 ⟨37,by decide⟩).lower ∧ (cell12409 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12409 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12409 ⟨38,by decide⟩).lower ∧ (cell12409 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12409 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12409 ⟨39,by decide⟩).lower ∧ (cell12409 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12409 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12409 ⟨40,by decide⟩).lower ∧ (cell12409 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12409 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12409 ⟨41,by decide⟩).lower ∧ (cell12409 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12409 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12409 ⟨42,by decide⟩).lower ∧ (cell12409 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12409 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12409 ⟨43,by decide⟩).lower ∧ (cell12409 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12409 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12409 ⟨44,by decide⟩).lower ∧ (cell12409 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12409 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12409 ⟨45,by decide⟩).lower ∧ (cell12409 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12409 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12409 ⟨46,by decide⟩).lower ∧ (cell12409 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12409 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12409 ⟨47,by decide⟩).lower ∧ (cell12409 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12409 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12409 ⟨48,by decide⟩).lower ∧ (cell12409 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12409 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12409 ⟨49,by decide⟩).lower ∧ (cell12409 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12409 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12409 ⟨50,by decide⟩).lower ∧ (cell12409 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12409 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12409 ⟨51,by decide⟩).lower ∧ (cell12409 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12409 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12409 ⟨52,by decide⟩).lower ∧ (cell12409 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12409 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12409 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12409 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12409,cell12409,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12409 i).lower ∧
    (cell12409 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12409 i).upper ≤ (0.532 : ℝ) ∧
    (cell12409 i).centre ≤ (0.1 : ℝ) ∧ (cell12409 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12409 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12409 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12409

/-! The local source numeric instances at 12409 have no network premises. -/
namespace BstLean.Part269.N12409
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12409)
open BstLean.Part268 (cell12409)

noncomputable def sourceNumerics12409 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12409 (cell12409 i)
      scalarRow12409.M scalarRow12409.H scalarRow12409.xi := by
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
    energy_allowance := scalarRow12409.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12409]
    centre_nonneg := (scalarRow12409.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12409])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12409
/-! Actual 12410 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12410 ≤ (1.036228905571 : ℝ) := by
  have hr : (111.400179533068 : ℝ) ≤ √(12410 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.400179533068 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12410 12410 (11 / 1000) ≤
    (0.008580660453 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12410) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.400179533068 : ℝ) ≤ √(12410 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12410)
  have hdiv : K / √(12410 : ℝ) ≤ K / 111.400179533068 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.400179533068 ≤ (0.008580660453 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12410.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12410 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12410 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12410 := gPlus_lower 12410
end BstLean.Part269.N12410

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12410
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036228905570 : ℝ) ≤ wn 12410 := by
  have hn : √(12410 : ℝ) ≤ 111.400179533069 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12410 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.400179533069 ≤ 2 / √(12410 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257871325 : ℝ) ≤ rhoBar 12410 BstLean.Part154.csC ∧
    rhoBar 12410 BstLean.Part154.csC ≤ 0.000257871724 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036228905570 : ℝ) / (1.295212 * 12410) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036228905571 : ℝ) / (1.29521 * 12410) := by gcongr
      _ ≤ (0.000257871724 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12410 BstLean.Part154.csC) ≤ 0.001031553394 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12410 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) ≤ 0.000196964380 ∧
    cc1 (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) ≤ 0.000125329698 ∧
    cc2 (rhoBar 12410 BstLean.Part154.csC) ≤ 0.000072754796 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12410 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12410 BstLean.Part154.csC * nuR (rhoBar 12410 BstLean.Part154.csC)) ≤ 0.000515760073 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257871724 : ℝ) * 0.001031553394 := by gcongr
      _ ≤ (0.000515760073 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12410 BstLean.Part154.csC) * nuR (rhoBar 12410 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031553394 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12410 BstLean.Part154.csC) * rhoBar 12410 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257871724 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257871724 / 2 + 0.399 * 0.001031553394 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196964380 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515760073 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125329698 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257871724 / 1.414213562 := by gcongr
      _ ≤ (0.000072754796 : ℝ) := by norm_num

end BstLean.Part269.N12410

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12410
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) ≤ 1.67537E-7 := by
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12410 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12410 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196964380 : ℝ) ^ 2 + 0.000125329698 ^ 2 + 3 * 0.000072754796 ^ 2 +
        2 * 0.797885 * 0.000196964380 * 0.000125329698 + 2 * 0.000196964380 * 0.000072754796 +
        4 * 0.797885 * 0.000125329698 * 0.000072754796 := by gcongr
    _ ≤ (1.67537E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12410 BstLean.Part154.csC Θ ≤ 0.002692919536 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12410 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12410 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036228905571 * 1.67537E-7 / (0.000257871325 : ℝ) := by gcongr
    _ ≤ 0.002692919536 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12410 BstLean.Part154.csC Θ ≤ 0.002989146002 + 0.000680455348 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12410 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036228905571 : ℝ) * ((2 * Θ * 0.000257871724 +
        (6863 / 10000) * 0.000257871724 * 12410 * 0.001031553394) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002989146002 + 0.000680455348 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12410 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12410 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12410 0.011 Θ ∧ gammaRatio 12410 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12410 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036228905571 : ℝ) * 0.525 / ((1 - 0.011) * 12410) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12410 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12410 0.011 Θ) :=
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
    badAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12410 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12410 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12410 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12410 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12410 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12410 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12410 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12410 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12410 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12410 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036228905571 : ℝ) * 12410 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004089146002 + 0.003373374884 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12410

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12410
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12410 BstLean.Part154.csC) (piBar (rhoBar 12410 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12410 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12410 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12410 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12410 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12410 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12410 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12410 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12410 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12410 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053100692790 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12410) ≤ 0.010720248263 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12410 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036228905571)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010720248263 + 2 * 0.737676 / 12410) := by gcongr
    _ ≤ (0.053100692790 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12410 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12410

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12410
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490147163 : ℝ) ≤ plow 12410 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12410) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366767817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413782757) : eMP 12410 0.011 xi bn ≤ 0.001216789245 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12410 : ℝ) * (1 - 0.011))) ≤ 0.000601564590 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413782757 / (12410 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601564590 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601564590 : ℝ) + 3.141593 * 0.053366767817 / (12410 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216789245 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366767817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413782757) : PiBarMP 12410 12 0.011 xi bn ≤ 0.163145565929 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12410 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037600302619 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.785784286613 : ℝ) ≤ √((12410 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.400179533068 : ℝ) ≤ √(12410 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12410) ≤ 0.125066299904 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037600302619 + 0.053366767817 * 1.772454 / (2 * (110.785784286613 : ℝ))) * (1 + 0.001216789245) +
        8 / (12410 * 111.400179533068) + 0.125066299904 := by gcongr
    _ ≤ (0.163145565929 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366767817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413782757) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284113176906) :
    parallelOracle 12410 0.011 xi bn cd ≤ 0.164163140736 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12410 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12410 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490147163 : ℝ) ≤ plow 12410 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.400179533068 : ℝ) ≤ √(12410 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284113176906 : ℝ) / (2 * 0.560490147163 * 111.400179533068)) * 0.163145565929 +
        0.284113176906 ^ 2 / (2 * 0.560490147163 * 111.400179533068) := by gcongr
    _ ≤ (0.164163140736 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366767817) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413782757)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284113176906) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12410 12410 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490147163 : ℝ) ≤ plow 12410 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.400179533068 : ℝ) ≤ √(12410 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12410 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12410 Θ 1.22 ≤ 0.011903935035 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.400179533068 := by gcongr <;> linarith
      _ ≤ (0.011903935035 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12410 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12410 12410 0.011 ≤ 0.008580660453 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12410 12410 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12410 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12410 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12410 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12410 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164163140736 + 0.011903935035 + (0.008580660453 : ℝ) *
        (1 + 2 * (0.284113176906 + 0.011903935035) / (0.560490147163 * 111.400179533068))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12410]

end BstLean.Part269.N12410

/-! The original eight local profiles supply actual 12410 moment certificates. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12410 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053366767817 ∧
    0 ≤ bN 12410 BstLean.Part154.csC (groupTheta g) ∧ bN 12410 BstLean.Part154.csC (groupTheta g) ≤ 0.001413782757 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12410 12410 0.011
      (momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12410 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12410 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12410 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231012484116 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12410 0.011
      (momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12410 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12410
/-! The actual computed-centre upper energy formula at 12410. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12410

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12410)
open BstLean.Part268 (cell12410)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086386476365
  | 2 => 0.087346893815
  | 3 => 0.088308217076
  | 4 => 0.089272486525
  | 5 => 0.090242146968
  | 6 => 0.091220104611
  | 7 => 0.092209788852
  | 8 => 0.093215218814
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12410 12410 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12410 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12410

/-! Actual upper energy certificates on all 43 source endpoints at 12410. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12410)
open BstLean.Part268 (cell12410)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12410 (gMinus 12410) (1 - (cell12410 i).lower) ≤ 1 ∧
    energyUpper 12410 (gMinus 12410) (BstLean.Part211.gPlus 12410)
      (finiteEnergy 12410 12410 0.011) (1 - (cell12410 i).lower) ≤
      (cell12410 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨10,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨11,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨12,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨13,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨14,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨15,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨16,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨17,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨18,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨19,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨20,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨21,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨22,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨23,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨24,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨25,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨26,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨27,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨28,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨29,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨30,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨31,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨32,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨33,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨34,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨35,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨36,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨37,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨38,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨39,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨40,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨41,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨42,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨43,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨44,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨45,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨46,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨47,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨48,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨49,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨50,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨51,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12410) (by norm_num)
        (q := 1 - (cell12410 ⟨52,by decide⟩).lower)
        (by norm_num [cell12410]) (by norm_num [cell12410])
      exact ⟨E.1,E.2.trans (by norm_num [cell12410])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12410

/-! Source-cell containment and simple scalar guards at 12410. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12410)
open BstLean.Part268 (cell12410)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12410 ⟨10,by decide⟩).lower ∧ (cell12410 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12410 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12410 ⟨11,by decide⟩).lower ∧ (cell12410 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12410 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12410 ⟨12,by decide⟩).lower ∧ (cell12410 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12410 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12410 ⟨13,by decide⟩).lower ∧ (cell12410 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12410 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12410 ⟨14,by decide⟩).lower ∧ (cell12410 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12410 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12410 ⟨15,by decide⟩).lower ∧ (cell12410 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12410 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12410 ⟨16,by decide⟩).lower ∧ (cell12410 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12410 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12410 ⟨17,by decide⟩).lower ∧ (cell12410 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12410 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12410 ⟨18,by decide⟩).lower ∧ (cell12410 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12410 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12410 ⟨19,by decide⟩).lower ∧ (cell12410 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12410 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12410 ⟨20,by decide⟩).lower ∧ (cell12410 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12410 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12410 ⟨21,by decide⟩).lower ∧ (cell12410 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12410 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12410 ⟨22,by decide⟩).lower ∧ (cell12410 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12410 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12410 ⟨23,by decide⟩).lower ∧ (cell12410 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12410 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12410 ⟨24,by decide⟩).lower ∧ (cell12410 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12410 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12410 ⟨25,by decide⟩).lower ∧ (cell12410 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12410 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12410 ⟨26,by decide⟩).lower ∧ (cell12410 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12410 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12410 ⟨27,by decide⟩).lower ∧ (cell12410 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12410 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12410 ⟨28,by decide⟩).lower ∧ (cell12410 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12410 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12410 ⟨29,by decide⟩).lower ∧ (cell12410 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12410 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12410 ⟨30,by decide⟩).lower ∧ (cell12410 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12410 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12410 ⟨31,by decide⟩).lower ∧ (cell12410 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12410 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12410 ⟨32,by decide⟩).lower ∧ (cell12410 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12410 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12410 ⟨33,by decide⟩).lower ∧ (cell12410 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12410 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12410 ⟨34,by decide⟩).lower ∧ (cell12410 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12410 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12410 ⟨35,by decide⟩).lower ∧ (cell12410 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12410 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12410 ⟨36,by decide⟩).lower ∧ (cell12410 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12410 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12410 ⟨37,by decide⟩).lower ∧ (cell12410 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12410 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12410 ⟨38,by decide⟩).lower ∧ (cell12410 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12410 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12410 ⟨39,by decide⟩).lower ∧ (cell12410 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12410 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12410 ⟨40,by decide⟩).lower ∧ (cell12410 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12410 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12410 ⟨41,by decide⟩).lower ∧ (cell12410 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12410 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12410 ⟨42,by decide⟩).lower ∧ (cell12410 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12410 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12410 ⟨43,by decide⟩).lower ∧ (cell12410 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12410 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12410 ⟨44,by decide⟩).lower ∧ (cell12410 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12410 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12410 ⟨45,by decide⟩).lower ∧ (cell12410 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12410 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12410 ⟨46,by decide⟩).lower ∧ (cell12410 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12410 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12410 ⟨47,by decide⟩).lower ∧ (cell12410 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12410 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12410 ⟨48,by decide⟩).lower ∧ (cell12410 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12410 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12410 ⟨49,by decide⟩).lower ∧ (cell12410 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12410 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12410 ⟨50,by decide⟩).lower ∧ (cell12410 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12410 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12410 ⟨51,by decide⟩).lower ∧ (cell12410 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12410 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12410 ⟨52,by decide⟩).lower ∧ (cell12410 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12410 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12410 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12410 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12410,cell12410,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12410 i).lower ∧
    (cell12410 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12410 i).upper ≤ (0.532 : ℝ) ∧
    (cell12410 i).centre ≤ (0.1 : ℝ) ∧ (cell12410 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12410 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12410 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12410

/-! The local source numeric instances at 12410 have no network premises. -/
namespace BstLean.Part269.N12410
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12410)
open BstLean.Part268 (cell12410)

noncomputable def sourceNumerics12410 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12410 (cell12410 i)
      scalarRow12410.M scalarRow12410.H scalarRow12410.xi := by
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
    energy_allowance := scalarRow12410.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12410]
    centre_nonneg := (scalarRow12410.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12410])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12410
/-! Actual 12411 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12411 ≤ (1.036227433009 : ℝ) := by
  have hr : (111.404667765762 : ℝ) ≤ √(12411 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.404667765762 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12411 12411 (11 / 1000) ≤
    (0.008580314756 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12411) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.404667765762 : ℝ) ≤ √(12411 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12411)
  have hdiv : K / √(12411 : ℝ) ≤ K / 111.404667765762 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.404667765762 ≤ (0.008580314756 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12411.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12411 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12411 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12411 := gPlus_lower 12411
end BstLean.Part269.N12411

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12411
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036227433008 : ℝ) ≤ wn 12411 := by
  have hn : √(12411 : ℝ) ≤ 111.404667765763 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12411 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.404667765763 ≤ 2 / √(12411 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257850181 : ℝ) ≤ rhoBar 12411 BstLean.Part154.csC ∧
    rhoBar 12411 BstLean.Part154.csC ≤ 0.000257850580 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036227433008 : ℝ) / (1.295212 * 12411) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036227433009 : ℝ) / (1.29521 * 12411) := by gcongr
      _ ≤ (0.000257850580 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12411 BstLean.Part154.csC) ≤ 0.001031468807 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12411 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) ≤ 0.000196948230 ∧
    cc1 (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) ≤ 0.000125319422 ∧
    cc2 (rhoBar 12411 BstLean.Part154.csC) ≤ 0.000072748830 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12411 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12411 BstLean.Part154.csC * nuR (rhoBar 12411 BstLean.Part154.csC)) ≤ 0.000515717782 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257850580 : ℝ) * 0.001031468807 := by gcongr
      _ ≤ (0.000515717782 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12411 BstLean.Part154.csC) * nuR (rhoBar 12411 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031468807 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12411 BstLean.Part154.csC) * rhoBar 12411 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257850580 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257850580 / 2 + 0.399 * 0.001031468807 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196948230 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515717782 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125319422 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257850580 / 1.414213562 := by gcongr
      _ ≤ (0.000072748830 : ℝ) := by norm_num

end BstLean.Part269.N12411

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12411
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) ≤ 1.67509E-7 := by
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12411 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12411 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196948230 : ℝ) ^ 2 + 0.000125319422 ^ 2 + 3 * 0.000072748830 ^ 2 +
        2 * 0.797885 * 0.000196948230 * 0.000125319422 + 2 * 0.000196948230 * 0.000072748830 +
        4 * 0.797885 * 0.000125319422 * 0.000072748830 := by gcongr
    _ ≤ (1.67509E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12411 BstLean.Part154.csC Θ ≤ 0.002692686434 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12411 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12411 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036227433009 * 1.67509E-7 / (0.000257850181 : ℝ) := by gcongr
    _ ≤ 0.002692686434 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12411 BstLean.Part154.csC Θ ≤ 0.002988892399 + 0.000680398587 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12411 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036227433009 : ℝ) * ((2 * Θ * 0.000257850580 +
        (6863 / 10000) * 0.000257850580 * 12411 * 0.001031468807) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002988892399 + 0.000680398587 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12411 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12411 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12411 0.011 Θ ∧ gammaRatio 12411 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12411 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036227433009 : ℝ) * 0.525 / ((1 - 0.011) * 12411) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12411 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12411 0.011 Θ) :=
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
    badAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12411 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12411 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12411 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12411 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12411 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12411 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12411 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12411 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12411 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12411 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036227433009 : ℝ) * 12411 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004088892399 + 0.003373085021 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12411

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12411
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12411 BstLean.Part154.csC) (piBar (rhoBar 12411 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12411 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12411 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12411 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12411 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12411 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12411 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12411 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12411 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12411 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053098530023 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12411) ≤ 0.010719816369 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12411 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036227433009)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010719816369 + 2 * 0.737676 / 12411) := by gcongr
    _ ≤ (0.053098530023 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12411 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12411

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12411
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490194520 : ℝ) ≤ plow 12411 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12411) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366362036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413660378) : eMP 12411 0.011 xi bn ≤ 0.001216687498 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12411 : ℝ) * (1 - 0.011))) ≤ 0.000601514319 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413660378 / (12411 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601514319 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601514319 : ℝ) + 3.141593 * 0.053366362036 / (12411 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216687498 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366362036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413660378) : PiBarMP 12411 12 0.011 xi bn ≤ 0.163138872880 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12411 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037598675217 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.790247765766 : ℝ) ≤ √((12411 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.404667765762 : ℝ) ≤ √(12411 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12411) ≤ 0.125061261276 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037598675217 + 0.053366362036 * 1.772454 / (2 * (110.790247765766 : ℝ))) * (1 + 0.001216687498) +
        8 / (12411 * 111.404667765762) + 0.125061261276 := by gcongr
    _ ≤ (0.163138872880 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366362036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413660378) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284110135870) :
    parallelOracle 12411 0.011 xi bn cd ≤ 0.164156373569 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12411 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12411 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490194520 : ℝ) ≤ plow 12411 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.404667765762 : ℝ) ≤ √(12411 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284110135870 : ℝ) / (2 * 0.560490194520 * 111.404667765762)) * 0.163138872880 +
        0.284110135870 ^ 2 / (2 * 0.560490194520 * 111.404667765762) := by gcongr
    _ ≤ (0.164156373569 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053366362036) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413660378)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284110135870) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12411 12411 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490194520 : ℝ) ≤ plow 12411 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.404667765762 : ℝ) ≤ √(12411 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12411 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12411 Θ 1.22 ≤ 0.011903455453 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.404667765762 := by gcongr <;> linarith
      _ ≤ (0.011903455453 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12411 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12411 12411 0.011 ≤ 0.008580314756 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12411 12411 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12411 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12411 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12411 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12411 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164156373569 + 0.011903455453 + (0.008580314756 : ℝ) *
        (1 + 2 * (0.284110135870 + 0.011903455453) / (0.560490194520 * 111.404667765762))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12411]

end BstLean.Part269.N12411

/-! The original eight local profiles supply actual 12411 moment certificates. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12411 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053366362036 ∧
    0 ≤ bN 12411 BstLean.Part154.csC (groupTheta g) ∧ bN 12411 BstLean.Part154.csC (groupTheta g) ≤ 0.001413660378 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12411 12411 0.011
      (momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12411 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12411 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12411 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231011605847 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12411 0.011
      (momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12411 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12411
/-! The actual computed-centre upper energy formula at 12411. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12411

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12411)
open BstLean.Part268 (cell12411)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086383193931
  | 2 => 0.087343542154
  | 3 => 0.088304784709
  | 4 => 0.089268959443
  | 5 => 0.090238508205
  | 6 => 0.091216333769
  | 7 => 0.092205861573
  | 8 => 0.093211106200
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12411 12411 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12411 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12411

/-! Actual upper energy certificates on all 43 source endpoints at 12411. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12411)
open BstLean.Part268 (cell12411)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12411 (gMinus 12411) (1 - (cell12411 i).lower) ≤ 1 ∧
    energyUpper 12411 (gMinus 12411) (BstLean.Part211.gPlus 12411)
      (finiteEnergy 12411 12411 0.011) (1 - (cell12411 i).lower) ≤
      (cell12411 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨10,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨11,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨12,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨13,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨14,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨15,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨16,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨17,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨18,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨19,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨20,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨21,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨22,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨23,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨24,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨25,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨26,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨27,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨28,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨29,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨30,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨31,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨32,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨33,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨34,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨35,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨36,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨37,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨38,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨39,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨40,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨41,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨42,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨43,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨44,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨45,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨46,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨47,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨48,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨49,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨50,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨51,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12411) (by norm_num)
        (q := 1 - (cell12411 ⟨52,by decide⟩).lower)
        (by norm_num [cell12411]) (by norm_num [cell12411])
      exact ⟨E.1,E.2.trans (by norm_num [cell12411])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12411

/-! Source-cell containment and simple scalar guards at 12411. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12411)
open BstLean.Part268 (cell12411)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12411 ⟨10,by decide⟩).lower ∧ (cell12411 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12411 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12411 ⟨11,by decide⟩).lower ∧ (cell12411 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12411 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12411 ⟨12,by decide⟩).lower ∧ (cell12411 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12411 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12411 ⟨13,by decide⟩).lower ∧ (cell12411 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12411 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12411 ⟨14,by decide⟩).lower ∧ (cell12411 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12411 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12411 ⟨15,by decide⟩).lower ∧ (cell12411 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12411 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12411 ⟨16,by decide⟩).lower ∧ (cell12411 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12411 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12411 ⟨17,by decide⟩).lower ∧ (cell12411 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12411 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12411 ⟨18,by decide⟩).lower ∧ (cell12411 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12411 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12411 ⟨19,by decide⟩).lower ∧ (cell12411 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12411 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12411 ⟨20,by decide⟩).lower ∧ (cell12411 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12411 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12411 ⟨21,by decide⟩).lower ∧ (cell12411 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12411 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12411 ⟨22,by decide⟩).lower ∧ (cell12411 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12411 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12411 ⟨23,by decide⟩).lower ∧ (cell12411 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12411 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12411 ⟨24,by decide⟩).lower ∧ (cell12411 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12411 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12411 ⟨25,by decide⟩).lower ∧ (cell12411 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12411 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12411 ⟨26,by decide⟩).lower ∧ (cell12411 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12411 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12411 ⟨27,by decide⟩).lower ∧ (cell12411 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12411 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12411 ⟨28,by decide⟩).lower ∧ (cell12411 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12411 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12411 ⟨29,by decide⟩).lower ∧ (cell12411 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12411 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12411 ⟨30,by decide⟩).lower ∧ (cell12411 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12411 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12411 ⟨31,by decide⟩).lower ∧ (cell12411 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12411 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12411 ⟨32,by decide⟩).lower ∧ (cell12411 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12411 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12411 ⟨33,by decide⟩).lower ∧ (cell12411 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12411 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12411 ⟨34,by decide⟩).lower ∧ (cell12411 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12411 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12411 ⟨35,by decide⟩).lower ∧ (cell12411 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12411 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12411 ⟨36,by decide⟩).lower ∧ (cell12411 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12411 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12411 ⟨37,by decide⟩).lower ∧ (cell12411 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12411 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12411 ⟨38,by decide⟩).lower ∧ (cell12411 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12411 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12411 ⟨39,by decide⟩).lower ∧ (cell12411 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12411 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12411 ⟨40,by decide⟩).lower ∧ (cell12411 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12411 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12411 ⟨41,by decide⟩).lower ∧ (cell12411 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12411 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12411 ⟨42,by decide⟩).lower ∧ (cell12411 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12411 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12411 ⟨43,by decide⟩).lower ∧ (cell12411 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12411 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12411 ⟨44,by decide⟩).lower ∧ (cell12411 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12411 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12411 ⟨45,by decide⟩).lower ∧ (cell12411 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12411 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12411 ⟨46,by decide⟩).lower ∧ (cell12411 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12411 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12411 ⟨47,by decide⟩).lower ∧ (cell12411 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12411 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12411 ⟨48,by decide⟩).lower ∧ (cell12411 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12411 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12411 ⟨49,by decide⟩).lower ∧ (cell12411 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12411 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12411 ⟨50,by decide⟩).lower ∧ (cell12411 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12411 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12411 ⟨51,by decide⟩).lower ∧ (cell12411 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12411 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12411 ⟨52,by decide⟩).lower ∧ (cell12411 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12411 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12411 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12411 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12411,cell12411,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12411 i).lower ∧
    (cell12411 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12411 i).upper ≤ (0.532 : ℝ) ∧
    (cell12411 i).centre ≤ (0.1 : ℝ) ∧ (cell12411 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12411 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12411 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12411

/-! The local source numeric instances at 12411 have no network premises. -/
namespace BstLean.Part269.N12411
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12411)
open BstLean.Part268 (cell12411)

noncomputable def sourceNumerics12411 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12411 (cell12411 i)
      scalarRow12411.M scalarRow12411.H scalarRow12411.xi := by
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
    energy_allowance := scalarRow12411.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12411]
    centre_nonneg := (scalarRow12411.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12411])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12411
/-! Actual 12412 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12412 ≤ (1.036225960625 : ℝ) := by
  have hr : (111.409155817643 : ℝ) ≤ √(12412 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.409155817643 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12412 12412 (11 / 1000) ≤
    (0.008579969100 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12412) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.409155817643 : ℝ) ≤ √(12412 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12412)
  have hdiv : K / √(12412 : ℝ) ≤ K / 111.409155817643 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.409155817643 ≤ (0.008579969100 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12412.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12412 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12412 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12412 := gPlus_lower 12412
end BstLean.Part269.N12412

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12412
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036225960624 : ℝ) ≤ wn 12412 := by
  have hn : √(12412 : ℝ) ≤ 111.409155817644 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12412 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.409155817644 ≤ 2 / √(12412 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257829041 : ℝ) ≤ rhoBar 12412 BstLean.Part154.csC ∧
    rhoBar 12412 BstLean.Part154.csC ≤ 0.000257829440 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036225960624 : ℝ) / (1.295212 * 12412) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036225960625 : ℝ) / (1.29521 * 12412) := by gcongr
      _ ≤ (0.000257829440 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12412 BstLean.Part154.csC) ≤ 0.001031384237 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12412 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) ≤ 0.000196932082 ∧
    cc1 (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) ≤ 0.000125309147 ∧
    cc2 (rhoBar 12412 BstLean.Part154.csC) ≤ 0.000072742866 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12412 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12412 BstLean.Part154.csC * nuR (rhoBar 12412 BstLean.Part154.csC)) ≤ 0.000515675499 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257829440 : ℝ) * 0.001031384237 := by gcongr
      _ ≤ (0.000515675499 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12412 BstLean.Part154.csC) * nuR (rhoBar 12412 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031384237 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12412 BstLean.Part154.csC) * rhoBar 12412 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257829440 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257829440 / 2 + 0.399 * 0.001031384237 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196932082 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515675499 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125309147 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257829440 / 1.414213562 := by gcongr
      _ ≤ (0.000072742866 : ℝ) := by norm_num

end BstLean.Part269.N12412

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12412
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) ≤ 1.67482E-7 := by
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12412 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12412 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196932082 : ℝ) ^ 2 + 0.000125309147 ^ 2 + 3 * 0.000072742866 ^ 2 +
        2 * 0.797885 * 0.000196932082 * 0.000125309147 + 2 * 0.000196932082 * 0.000072742866 +
        4 * 0.797885 * 0.000125309147 * 0.000072742866 := by gcongr
    _ ≤ (1.67482E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12412 BstLean.Part154.csC Θ ≤ 0.002692469331 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12412 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12412 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036225960625 * 1.67482E-7 / (0.000257829041 : ℝ) := by gcongr
    _ ≤ 0.002692469331 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12412 BstLean.Part154.csC Θ ≤ 0.002988638855 + 0.000680341838 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12412 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036225960625 : ℝ) * ((2 * Θ * 0.000257829440 +
        (6863 / 10000) * 0.000257829440 * 12412 * 0.001031384237) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002988638855 + 0.000680341838 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12412 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12412 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12412 0.011 Θ ∧ gammaRatio 12412 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12412 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036225960625 : ℝ) * 0.525 / ((1 - 0.011) * 12412) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12412 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12412 0.011 Θ) :=
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
    badAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12412 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12412 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12412 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12412 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12412 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12412 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12412 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12412 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12412 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12412 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036225960625 : ℝ) * 12412 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004088638855 + 0.003372811169 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12412

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12412
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12412 BstLean.Part154.csC) (piBar (rhoBar 12412 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12412 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12412 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12412 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12412 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12412 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12412 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12412 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12412 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12412 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053096367523 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12412) ≤ 0.010719384528 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12412 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036225960625)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010719384528 + 2 * 0.737676 / 12412) := by gcongr
    _ ≤ (0.053096367523 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12412 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12412

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12412
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490241870 : ℝ) ≤ plow 12412 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12412) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365964719)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413546399) : eMP 12412 0.011 xi bn ≤ 0.001216589334 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12412 : ℝ) * (1 - 0.011))) ≤ 0.000601465838 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413546399 / (12412 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601465838 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601465838 : ℝ) + 3.141593 * 0.053365964719 / (12412 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216589334 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365964719)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413546399) : PiBarMP 12412 12 0.011 xi bn ≤ 0.163132292423 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12412 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037597159454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.794711065104 : ℝ) ≤ √((12412 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.409155817643 : ℝ) ≤ √(12412 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12412) ≤ 0.125056223257 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037597159454 + 0.053365964719 * 1.772454 / (2 * (110.794711065104 : ℝ))) * (1 + 0.001216589334) +
        8 / (12412 * 111.409155817643) + 0.125056223257 := by gcongr
    _ ≤ (0.163132292423 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365964719)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413546399) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284107113419) :
    parallelOracle 12412 0.011 xi bn cd ≤ 0.164149719367 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12412 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12412 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490241870 : ℝ) ≤ plow 12412 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.409155817643 : ℝ) ≤ √(12412 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284107113419 : ℝ) / (2 * 0.560490241870 * 111.409155817643)) * 0.163132292423 +
        0.284107113419 ^ 2 / (2 * 0.560490241870 * 111.409155817643) := by gcongr
    _ ≤ (0.164149719367 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365964719) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413546399)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284107113419) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12412 12412 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490241870 : ℝ) ≤ plow 12412 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.409155817643 : ℝ) ≤ √(12412 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12412 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12412 Θ 1.22 ≤ 0.011902975930 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.409155817643 := by gcongr <;> linarith
      _ ≤ (0.011902975930 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12412 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12412 12412 0.011 ≤ 0.008579969100 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12412 12412 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12412 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12412 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12412 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12412 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164149719367 + 0.011902975930 + (0.008579969100 : ℝ) *
        (1 + 2 * (0.284107113419 + 0.011902975930) / (0.560490241870 * 111.409155817643))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12412]

end BstLean.Part269.N12412

/-! The original eight local profiles supply actual 12412 moment certificates. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12412 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053365964719 ∧
    0 ≤ bN 12412 BstLean.Part154.csC (groupTheta g) ∧ bN 12412 BstLean.Part154.csC (groupTheta g) ≤ 0.001413546399 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12412 12412 0.011
      (momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12412 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12412 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12412 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231010745896 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12412 0.011
      (momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12412 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12412
/-! The actual computed-centre upper energy formula at 12412. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12412

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12412)
open BstLean.Part268 (cell12412)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086379912967
  | 2 => 0.087340192028
  | 3 => 0.088301353956
  | 4 => 0.089265434073
  | 5 => 0.090234871273
  | 6 => 0.091212564903
  | 7 => 0.092201936445
  | 8 => 0.093206995946
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12412 12412 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12412 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12412

/-! Actual upper energy certificates on all 43 source endpoints at 12412. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12412)
open BstLean.Part268 (cell12412)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12412 (gMinus 12412) (1 - (cell12412 i).lower) ≤ 1 ∧
    energyUpper 12412 (gMinus 12412) (BstLean.Part211.gPlus 12412)
      (finiteEnergy 12412 12412 0.011) (1 - (cell12412 i).lower) ≤
      (cell12412 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨10,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨11,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨12,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨13,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨14,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨15,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨16,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨17,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨18,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨19,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨20,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨21,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨22,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨23,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨24,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨25,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨26,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨27,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨28,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨29,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨30,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨31,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨32,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨33,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨34,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨35,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨36,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨37,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨38,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨39,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨40,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨41,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨42,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨43,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨44,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨45,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨46,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨47,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨48,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨49,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨50,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨51,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12412) (by norm_num)
        (q := 1 - (cell12412 ⟨52,by decide⟩).lower)
        (by norm_num [cell12412]) (by norm_num [cell12412])
      exact ⟨E.1,E.2.trans (by norm_num [cell12412])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12412

/-! Source-cell containment and simple scalar guards at 12412. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12412)
open BstLean.Part268 (cell12412)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12412 ⟨10,by decide⟩).lower ∧ (cell12412 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12412 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12412 ⟨11,by decide⟩).lower ∧ (cell12412 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12412 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12412 ⟨12,by decide⟩).lower ∧ (cell12412 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12412 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12412 ⟨13,by decide⟩).lower ∧ (cell12412 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12412 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12412 ⟨14,by decide⟩).lower ∧ (cell12412 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12412 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12412 ⟨15,by decide⟩).lower ∧ (cell12412 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12412 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12412 ⟨16,by decide⟩).lower ∧ (cell12412 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12412 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12412 ⟨17,by decide⟩).lower ∧ (cell12412 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12412 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12412 ⟨18,by decide⟩).lower ∧ (cell12412 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12412 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12412 ⟨19,by decide⟩).lower ∧ (cell12412 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12412 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12412 ⟨20,by decide⟩).lower ∧ (cell12412 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12412 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12412 ⟨21,by decide⟩).lower ∧ (cell12412 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12412 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12412 ⟨22,by decide⟩).lower ∧ (cell12412 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12412 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12412 ⟨23,by decide⟩).lower ∧ (cell12412 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12412 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12412 ⟨24,by decide⟩).lower ∧ (cell12412 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12412 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12412 ⟨25,by decide⟩).lower ∧ (cell12412 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12412 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12412 ⟨26,by decide⟩).lower ∧ (cell12412 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12412 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12412 ⟨27,by decide⟩).lower ∧ (cell12412 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12412 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12412 ⟨28,by decide⟩).lower ∧ (cell12412 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12412 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12412 ⟨29,by decide⟩).lower ∧ (cell12412 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12412 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12412 ⟨30,by decide⟩).lower ∧ (cell12412 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12412 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12412 ⟨31,by decide⟩).lower ∧ (cell12412 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12412 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12412 ⟨32,by decide⟩).lower ∧ (cell12412 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12412 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12412 ⟨33,by decide⟩).lower ∧ (cell12412 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12412 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12412 ⟨34,by decide⟩).lower ∧ (cell12412 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12412 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12412 ⟨35,by decide⟩).lower ∧ (cell12412 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12412 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12412 ⟨36,by decide⟩).lower ∧ (cell12412 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12412 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12412 ⟨37,by decide⟩).lower ∧ (cell12412 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12412 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12412 ⟨38,by decide⟩).lower ∧ (cell12412 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12412 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12412 ⟨39,by decide⟩).lower ∧ (cell12412 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12412 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12412 ⟨40,by decide⟩).lower ∧ (cell12412 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12412 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12412 ⟨41,by decide⟩).lower ∧ (cell12412 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12412 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12412 ⟨42,by decide⟩).lower ∧ (cell12412 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12412 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12412 ⟨43,by decide⟩).lower ∧ (cell12412 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12412 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12412 ⟨44,by decide⟩).lower ∧ (cell12412 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12412 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12412 ⟨45,by decide⟩).lower ∧ (cell12412 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12412 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12412 ⟨46,by decide⟩).lower ∧ (cell12412 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12412 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12412 ⟨47,by decide⟩).lower ∧ (cell12412 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12412 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12412 ⟨48,by decide⟩).lower ∧ (cell12412 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12412 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12412 ⟨49,by decide⟩).lower ∧ (cell12412 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12412 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12412 ⟨50,by decide⟩).lower ∧ (cell12412 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12412 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12412 ⟨51,by decide⟩).lower ∧ (cell12412 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12412 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12412 ⟨52,by decide⟩).lower ∧ (cell12412 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12412 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12412 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12412 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12412,cell12412,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12412 i).lower ∧
    (cell12412 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12412 i).upper ≤ (0.532 : ℝ) ∧
    (cell12412 i).centre ≤ (0.1 : ℝ) ∧ (cell12412 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12412 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12412 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12412

/-! The local source numeric instances at 12412 have no network premises. -/
namespace BstLean.Part269.N12412
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12412)
open BstLean.Part268 (cell12412)

noncomputable def sourceNumerics12412 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12412 (cell12412 i)
      scalarRow12412.M scalarRow12412.H scalarRow12412.xi := by
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
    energy_allowance := scalarRow12412.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12412]
    centre_nonneg := (scalarRow12412.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12412])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12412