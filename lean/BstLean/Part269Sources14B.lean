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
/-! Actual 12713 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12713 ≤ (1.035790746517 : ℝ) := by
  have hr : (112.751940116345 : ℝ) ≤ √(12713 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.751940116345 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12713 12713 (11 / 1000) ≤
    (0.008477787827 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12713) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.751940116345 : ℝ) ≤ √(12713 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12713)
  have hdiv : K / √(12713 : ℝ) ≤ K / 112.751940116345 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.751940116345 ≤ (0.008477787827 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12713.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12713 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12713 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12713 := gPlus_lower 12713
end BstLean.Part269.N12713

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12713
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035790746516 : ℝ) ≤ wn 12713 := by
  have hn : √(12713 : ℝ) ≤ 112.751940116346 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12713 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.751940116346 ≤ 2 / √(12713 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251618814 : ℝ) ≤ rhoBar 12713 BstLean.Part154.csC ∧
    rhoBar 12713 BstLean.Part154.csC ≤ 0.000251619203 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035790746516 : ℝ) / (1.295212 * 12713) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035790746517 : ℝ) / (1.29521 * 12713) := by gcongr
      _ ≤ (0.000251619203 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12713 BstLean.Part154.csC) ≤ 0.001006540125 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12713 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) ≤ 0.000192188435 ∧
    cc1 (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) ≤ 0.000122290780 ∧
    cc2 (rhoBar 12713 BstLean.Part154.csC) ≤ 0.000070990737 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12713 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12713 BstLean.Part154.csC * nuR (rhoBar 12713 BstLean.Part154.csC)) ≤ 0.000503254235 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251619203 : ℝ) * 0.001006540125 := by gcongr
      _ ≤ (0.000503254235 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12713 BstLean.Part154.csC) * nuR (rhoBar 12713 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006540125 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12713 BstLean.Part154.csC) * rhoBar 12713 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251619203 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251619203 / 2 + 0.399 * 0.001006540125 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192188435 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503254235 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122290780 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251619203 / 1.414213562 := by gcongr
      _ ≤ (0.000070990737 : ℝ) := by norm_num

end BstLean.Part269.N12713

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12713
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) ≤ 1.59511E-7 := by
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12713 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12713 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192188435 : ℝ) ^ 2 + 0.000122290780 ^ 2 + 3 * 0.000070990737 ^ 2 +
        2 * 0.797885 * 0.000192188435 * 0.000122290780 + 2 * 0.000192188435 * 0.000070990737 +
        4 * 0.797885 * 0.000122290780 * 0.000070990737 := by gcongr
    _ ≤ (1.59511E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12713 BstLean.Part154.csC Θ ≤ 0.002626512941 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12713 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12713 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035790746517 * 1.59511E-7 / (0.000251618814 : ℝ) := by gcongr
    _ ≤ 0.002626512941 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12713 BstLean.Part154.csC Θ ≤ 0.002914198676 + 0.000663675849 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12713 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035790746517 : ℝ) * ((2 * Θ * 0.000251619203 +
        (6863 / 10000) * 0.000251619203 * 12713 * 0.001006540125) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002914198676 + 0.000663675849 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12713 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12713 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12713 0.011 Θ ∧ gammaRatio 12713 0.011 Θ ≤ 0.000086500176 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12713 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035790746517 : ℝ) * 0.525 / ((1 - 0.011) * 12713) := by gcongr
      _ ≤ (0.000086500176 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12713 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12713 0.011 Θ) :=
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
    badAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12713 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12713 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12713 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12713 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12713 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12713 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12713 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12713 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12713 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12713 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035790746517 : ℝ) * 12713 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003529891153 + 0.003290188790 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12713

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12713
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12713 BstLean.Part154.csC) (piBar (rhoBar 12713 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12713 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12713 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12713 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12713 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12713 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12713 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12713 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12713 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12713 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052457180448 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12713) ≤ 0.010591725339 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12713 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035790746517)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010591725339 + 2 * 0.737676 / 12713) := by gcongr
    _ ≤ (0.052457180448 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12713 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12713

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12713
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504155588 : ℝ) ≤ plow 12713 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12713) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763840268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378919295) : eMP 12713 0.011 xi bn ≤ 0.001187140900 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12713 : ℝ) * (1 - 0.011))) ≤ 0.000586978529 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378919295 / (12713 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586978529 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586978529 : ℝ) + 3.141593 * 0.052763840268 / (12713 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187140900 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763840268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378919295) : PiBarMP 12713 12 0.011 xi bn ≤ 0.161167888928 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12713 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037133802593 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.130089628074 : ℝ) ≤ √((12713 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.751940116345 : ℝ) ≤ √(12713 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12713) ≤ 0.123566904910 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037133802593 + 0.052763840268 * 1.772454 / (2 * (112.130089628074 : ℝ))) * (1 + 0.001187140900) +
        8 / (12713 * 112.751940116345) + 0.123566904910 := by gcongr
    _ ≤ (0.161167888928 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763840268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378919295) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282160990317) :
    parallelOracle 12713 0.011 xi bn cd ≤ 0.162157558318 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12713 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12713 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504155588 : ℝ) ≤ plow 12713 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.751940116345 : ℝ) ≤ √(12713 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282160990317 : ℝ) / (2 * 0.560504155588 * 112.751940116345)) * 0.161167888928 +
        0.282160990317 ^ 2 / (2 * 0.560504155588 * 112.751940116345) := by gcongr
    _ ≤ (0.162157558318 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763840268) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378919295)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282160990317) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12713 12713 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504155588 : ℝ) ≤ plow 12713 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.751940116345 : ℝ) ≤ √(12713 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12713 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12713 Θ 1.22 ≤ 0.011761221126 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.751940116345 := by gcongr <;> linarith
      _ ≤ (0.011761221126 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12713 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12713 12713 0.011 ≤ 0.008477787827 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12713 12713 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12713 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12713 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12713 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12713 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162157558318 + 0.011761221126 + (0.008477787827 : ℝ) *
        (1 + 2 * (0.282160990317 + 0.011761221126) / (0.560504155588 * 112.751940116345))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12713]

end BstLean.Part269.N12713

/-! The original eight local profiles supply actual 12713 moment certificates. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12713 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052763840268 ∧
    0 ≤ bN 12713 BstLean.Part154.csC (groupTheta g) ∧ bN 12713 BstLean.Part154.csC (groupTheta g) ≤ 0.001378919295 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12713 12713 0.011
      (momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12713 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12713 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12713 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229703809869 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12713 0.011
      (momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12713 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12713
/-! The actual computed-centre upper energy formula at 12713. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12713

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12713)
open BstLean.Part268 (cell12713)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085452435574
  | 2 => 0.086394492056
  | 3 => 0.087334587435
  | 4 => 0.088274116544
  | 5 => 0.089214767269
  | 6 => 0.090158564186
  | 7 => 0.091107916302
  | 8 => 0.092065668974
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12713 12713 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12713 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12713

/-! Actual upper energy certificates on all 43 source endpoints at 12713. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12713)
open BstLean.Part268 (cell12713)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12713 (gMinus 12713) (1 - (cell12713 i).lower) ≤ 1 ∧
    energyUpper 12713 (gMinus 12713) (BstLean.Part211.gPlus 12713)
      (finiteEnergy 12713 12713 0.011) (1 - (cell12713 i).lower) ≤
      (cell12713 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨10,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨11,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨12,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨13,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨14,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨15,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨16,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨17,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨18,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨19,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨20,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨21,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨22,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨23,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨24,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨25,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨26,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨27,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨28,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨29,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨30,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨31,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨32,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨33,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨34,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨35,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨36,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨37,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨38,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨39,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨40,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨41,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨42,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨43,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨44,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨45,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨46,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨47,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨48,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨49,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨50,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨51,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12713) (by norm_num)
        (q := 1 - (cell12713 ⟨52,by decide⟩).lower)
        (by norm_num [cell12713]) (by norm_num [cell12713])
      exact ⟨E.1,E.2.trans (by norm_num [cell12713])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12713

/-! Source-cell containment and simple scalar guards at 12713. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12713)
open BstLean.Part268 (cell12713)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12713 ⟨10,by decide⟩).lower ∧ (cell12713 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12713 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12713 ⟨11,by decide⟩).lower ∧ (cell12713 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12713 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12713 ⟨12,by decide⟩).lower ∧ (cell12713 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12713 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12713 ⟨13,by decide⟩).lower ∧ (cell12713 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12713 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12713 ⟨14,by decide⟩).lower ∧ (cell12713 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12713 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12713 ⟨15,by decide⟩).lower ∧ (cell12713 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12713 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12713 ⟨16,by decide⟩).lower ∧ (cell12713 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12713 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12713 ⟨17,by decide⟩).lower ∧ (cell12713 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12713 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12713 ⟨18,by decide⟩).lower ∧ (cell12713 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12713 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12713 ⟨19,by decide⟩).lower ∧ (cell12713 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12713 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12713 ⟨20,by decide⟩).lower ∧ (cell12713 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12713 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12713 ⟨21,by decide⟩).lower ∧ (cell12713 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12713 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12713 ⟨22,by decide⟩).lower ∧ (cell12713 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12713 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12713 ⟨23,by decide⟩).lower ∧ (cell12713 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12713 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12713 ⟨24,by decide⟩).lower ∧ (cell12713 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12713 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12713 ⟨25,by decide⟩).lower ∧ (cell12713 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12713 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12713 ⟨26,by decide⟩).lower ∧ (cell12713 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12713 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12713 ⟨27,by decide⟩).lower ∧ (cell12713 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12713 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12713 ⟨28,by decide⟩).lower ∧ (cell12713 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12713 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12713 ⟨29,by decide⟩).lower ∧ (cell12713 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12713 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12713 ⟨30,by decide⟩).lower ∧ (cell12713 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12713 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12713 ⟨31,by decide⟩).lower ∧ (cell12713 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12713 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12713 ⟨32,by decide⟩).lower ∧ (cell12713 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12713 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12713 ⟨33,by decide⟩).lower ∧ (cell12713 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12713 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12713 ⟨34,by decide⟩).lower ∧ (cell12713 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12713 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12713 ⟨35,by decide⟩).lower ∧ (cell12713 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12713 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12713 ⟨36,by decide⟩).lower ∧ (cell12713 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12713 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12713 ⟨37,by decide⟩).lower ∧ (cell12713 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12713 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12713 ⟨38,by decide⟩).lower ∧ (cell12713 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12713 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12713 ⟨39,by decide⟩).lower ∧ (cell12713 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12713 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12713 ⟨40,by decide⟩).lower ∧ (cell12713 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12713 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12713 ⟨41,by decide⟩).lower ∧ (cell12713 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12713 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12713 ⟨42,by decide⟩).lower ∧ (cell12713 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12713 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12713 ⟨43,by decide⟩).lower ∧ (cell12713 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12713 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12713 ⟨44,by decide⟩).lower ∧ (cell12713 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12713 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12713 ⟨45,by decide⟩).lower ∧ (cell12713 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12713 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12713 ⟨46,by decide⟩).lower ∧ (cell12713 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12713 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12713 ⟨47,by decide⟩).lower ∧ (cell12713 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12713 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12713 ⟨48,by decide⟩).lower ∧ (cell12713 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12713 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12713 ⟨49,by decide⟩).lower ∧ (cell12713 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12713 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12713 ⟨50,by decide⟩).lower ∧ (cell12713 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12713 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12713 ⟨51,by decide⟩).lower ∧ (cell12713 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12713 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12713 ⟨52,by decide⟩).lower ∧ (cell12713 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12713 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12713 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12713 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12713,cell12713,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12713 i).lower ∧
    (cell12713 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12713 i).upper ≤ (0.532 : ℝ) ∧
    (cell12713 i).centre ≤ (0.1 : ℝ) ∧ (cell12713 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12713 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12713 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12713

/-! The local source numeric instances at 12713 have no network premises. -/
namespace BstLean.Part269.N12713
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12713)
open BstLean.Part268 (cell12713)

noncomputable def sourceNumerics12713 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12713 (cell12713 i)
      scalarRow12713.M scalarRow12713.H scalarRow12713.xi := by
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
    energy_allowance := scalarRow12713.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12713]
    centre_nonneg := (scalarRow12713.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12713])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12713
/-! Actual 12714 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12714 ≤ (1.035789326583 : ℝ) := by
  have hr : (112.756374542639 : ℝ) ≤ √(12714 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.756374542639 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12714 12714 (11 / 1000) ≤
    (0.008477454414 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12714) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.756374542639 : ℝ) ≤ √(12714 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12714)
  have hdiv : K / √(12714 : ℝ) ≤ K / 112.756374542639 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.756374542639 ≤ (0.008477454414 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12714.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12714 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12714 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12714 := gPlus_lower 12714
end BstLean.Part269.N12714

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12714
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035789326582 : ℝ) ≤ wn 12714 := by
  have hn : √(12714 : ℝ) ≤ 112.756374542640 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12714 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.756374542640 ≤ 2 / √(12714 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251598678 : ℝ) ≤ rhoBar 12714 BstLean.Part154.csC ∧
    rhoBar 12714 BstLean.Part154.csC ≤ 0.000251599068 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035789326582 : ℝ) / (1.295212 * 12714) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035789326583 : ℝ) / (1.29521 * 12714) := by gcongr
      _ ≤ (0.000251599068 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12714 BstLean.Part154.csC) ≤ 0.001006459575 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12714 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) ≤ 0.000192173056 ∧
    cc1 (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) ≤ 0.000122280993 ∧
    cc2 (rhoBar 12714 BstLean.Part154.csC) ≤ 0.000070985056 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12714 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12714 BstLean.Part154.csC * nuR (rhoBar 12714 BstLean.Part154.csC)) ≤ 0.000503213962 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251599068 : ℝ) * 0.001006459575 := by gcongr
      _ ≤ (0.000503213962 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12714 BstLean.Part154.csC) * nuR (rhoBar 12714 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006459575 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12714 BstLean.Part154.csC) * rhoBar 12714 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251599068 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251599068 / 2 + 0.399 * 0.001006459575 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192173056 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503213962 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122280993 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251599068 / 1.414213562 := by gcongr
      _ ≤ (0.000070985056 : ℝ) := by norm_num

end BstLean.Part269.N12714

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12714
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) ≤ 1.59485E-7 := by
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12714 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12714 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192173056 : ℝ) ^ 2 + 0.000122280993 ^ 2 + 3 * 0.000070985056 ^ 2 +
        2 * 0.797885 * 0.000192173056 * 0.000122280993 + 2 * 0.000192173056 * 0.000070985056 +
        4 * 0.797885 * 0.000122280993 * 0.000070985056 := by gcongr
    _ ≤ (1.59485E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12714 BstLean.Part154.csC Θ ≤ 0.002626291395 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12714 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12714 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035789326583 * 1.59485E-7 / (0.000251598678 : ℝ) := by gcongr
    _ ≤ 0.002626291395 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12714 BstLean.Part154.csC Θ ≤ 0.002913957481 + 0.000663621831 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12714 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035789326583 : ℝ) * ((2 * Θ * 0.000251599068 +
        (6863 / 10000) * 0.000251599068 * 12714 * 0.001006459575) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002913957481 + 0.000663621831 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12714 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12714 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12714 0.011 Θ ∧ gammaRatio 12714 0.011 Θ ≤ 0.000086493254 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12714 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035789326583 : ℝ) * 0.525 / ((1 - 0.011) * 12714) := by gcongr
      _ ≤ (0.000086493254 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12714 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12714 0.011 Θ) :=
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
    badAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12714 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12714 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12714 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12714 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12714 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12714 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12714 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12714 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12714 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12714 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035789326583 : ℝ) * 12714 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003529649958 + 0.003289913226 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12714

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12714
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12714 BstLean.Part154.csC) (piBar (rhoBar 12714 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12714 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12714 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12714 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12714 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12714 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12714 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12714 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12714 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12714 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052455095081 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12714) ≤ 0.010591308793 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12714 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035789326583)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010591308793 + 2 * 0.737676 / 12714) := by gcongr
    _ ≤ (0.052455095081 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12714 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12714

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12714
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504200715 : ℝ) ≤ plow 12714 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12714) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763454402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378802983) : eMP 12714 0.011 xi bn ≤ 0.001187044087 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12714 : ℝ) * (1 - 0.011))) ≤ 0.000586930689 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378802983 / (12714 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586930689 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586930689 : ℝ) + 3.141593 * 0.052763454402 / (12714 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187044087 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763454402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378802983) : PiBarMP 12714 12 0.011 xi bn ≤ 0.161161437572 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12714 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037132236440 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.134499597581 : ℝ) ≤ √((12714 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.756374542639 : ℝ) ≤ √(12714 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12714) ≤ 0.123562045333 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037132236440 + 0.052763454402 * 1.772454 / (2 * (112.134499597581 : ℝ))) * (1 + 0.001187044087) +
        8 / (12714 * 112.756374542639) + 0.123562045333 := by gcongr
    _ ≤ (0.161161437572 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763454402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378802983) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282158065027) :
    parallelOracle 12714 0.011 xi bn cd ≤ 0.162151036771 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12714 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12714 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504200715 : ℝ) ≤ plow 12714 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.756374542639 : ℝ) ≤ √(12714 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282158065027 : ℝ) / (2 * 0.560504200715 * 112.756374542639)) * 0.161161437572 +
        0.282158065027 ^ 2 / (2 * 0.560504200715 * 112.756374542639) := by gcongr
    _ ≤ (0.162151036771 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763454402) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378802983)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282158065027) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12714 12714 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504200715 : ℝ) ≤ plow 12714 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.756374542639 : ℝ) ≤ √(12714 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12714 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12714 Θ 1.22 ≤ 0.011760758586 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.756374542639 := by gcongr <;> linarith
      _ ≤ (0.011760758586 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12714 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12714 12714 0.011 ≤ 0.008477454414 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12714 12714 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12714 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12714 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12714 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12714 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162151036771 + 0.011760758586 + (0.008477454414 : ℝ) *
        (1 + 2 * (0.282158065027 + 0.011760758586) / (0.560504200715 * 112.756374542639))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12714]

end BstLean.Part269.N12714

/-! The original eight local profiles supply actual 12714 moment certificates. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12714 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052763454402 ∧
    0 ≤ bN 12714 BstLean.Part154.csC (groupTheta g) ∧ bN 12714 BstLean.Part154.csC (groupTheta g) ≤ 0.001378802983 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12714 12714 0.011
      (momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12714 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12714 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12714 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229702969946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12714 0.011
      (momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12714 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12714
/-! The actual computed-centre upper energy formula at 12714. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12714

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12714)
open BstLean.Part268 (cell12714)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085449533814
  | 2 => 0.086391537312
  | 3 => 0.087331572032
  | 4 => 0.088271031032
  | 5 => 0.089211600117
  | 6 => 0.090155301419
  | 7 => 0.091104541117
  | 8 => 0.092062161298
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12714 12714 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12714 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12714

/-! Actual upper energy certificates on all 43 source endpoints at 12714. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12714)
open BstLean.Part268 (cell12714)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12714 (gMinus 12714) (1 - (cell12714 i).lower) ≤ 1 ∧
    energyUpper 12714 (gMinus 12714) (BstLean.Part211.gPlus 12714)
      (finiteEnergy 12714 12714 0.011) (1 - (cell12714 i).lower) ≤
      (cell12714 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨10,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨11,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨12,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨13,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨14,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨15,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨16,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨17,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨18,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨19,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨20,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨21,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨22,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨23,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨24,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨25,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨26,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨27,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨28,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨29,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨30,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨31,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨32,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨33,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨34,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨35,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨36,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨37,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨38,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨39,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨40,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨41,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨42,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨43,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨44,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨45,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨46,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨47,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨48,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨49,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨50,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨51,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12714) (by norm_num)
        (q := 1 - (cell12714 ⟨52,by decide⟩).lower)
        (by norm_num [cell12714]) (by norm_num [cell12714])
      exact ⟨E.1,E.2.trans (by norm_num [cell12714])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12714

/-! Source-cell containment and simple scalar guards at 12714. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12714)
open BstLean.Part268 (cell12714)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12714 ⟨10,by decide⟩).lower ∧ (cell12714 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12714 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12714 ⟨11,by decide⟩).lower ∧ (cell12714 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12714 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12714 ⟨12,by decide⟩).lower ∧ (cell12714 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12714 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12714 ⟨13,by decide⟩).lower ∧ (cell12714 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12714 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12714 ⟨14,by decide⟩).lower ∧ (cell12714 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12714 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12714 ⟨15,by decide⟩).lower ∧ (cell12714 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12714 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12714 ⟨16,by decide⟩).lower ∧ (cell12714 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12714 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12714 ⟨17,by decide⟩).lower ∧ (cell12714 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12714 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12714 ⟨18,by decide⟩).lower ∧ (cell12714 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12714 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12714 ⟨19,by decide⟩).lower ∧ (cell12714 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12714 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12714 ⟨20,by decide⟩).lower ∧ (cell12714 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12714 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12714 ⟨21,by decide⟩).lower ∧ (cell12714 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12714 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12714 ⟨22,by decide⟩).lower ∧ (cell12714 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12714 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12714 ⟨23,by decide⟩).lower ∧ (cell12714 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12714 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12714 ⟨24,by decide⟩).lower ∧ (cell12714 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12714 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12714 ⟨25,by decide⟩).lower ∧ (cell12714 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12714 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12714 ⟨26,by decide⟩).lower ∧ (cell12714 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12714 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12714 ⟨27,by decide⟩).lower ∧ (cell12714 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12714 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12714 ⟨28,by decide⟩).lower ∧ (cell12714 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12714 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12714 ⟨29,by decide⟩).lower ∧ (cell12714 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12714 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12714 ⟨30,by decide⟩).lower ∧ (cell12714 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12714 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12714 ⟨31,by decide⟩).lower ∧ (cell12714 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12714 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12714 ⟨32,by decide⟩).lower ∧ (cell12714 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12714 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12714 ⟨33,by decide⟩).lower ∧ (cell12714 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12714 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12714 ⟨34,by decide⟩).lower ∧ (cell12714 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12714 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12714 ⟨35,by decide⟩).lower ∧ (cell12714 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12714 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12714 ⟨36,by decide⟩).lower ∧ (cell12714 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12714 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12714 ⟨37,by decide⟩).lower ∧ (cell12714 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12714 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12714 ⟨38,by decide⟩).lower ∧ (cell12714 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12714 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12714 ⟨39,by decide⟩).lower ∧ (cell12714 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12714 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12714 ⟨40,by decide⟩).lower ∧ (cell12714 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12714 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12714 ⟨41,by decide⟩).lower ∧ (cell12714 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12714 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12714 ⟨42,by decide⟩).lower ∧ (cell12714 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12714 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12714 ⟨43,by decide⟩).lower ∧ (cell12714 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12714 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12714 ⟨44,by decide⟩).lower ∧ (cell12714 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12714 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12714 ⟨45,by decide⟩).lower ∧ (cell12714 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12714 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12714 ⟨46,by decide⟩).lower ∧ (cell12714 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12714 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12714 ⟨47,by decide⟩).lower ∧ (cell12714 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12714 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12714 ⟨48,by decide⟩).lower ∧ (cell12714 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12714 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12714 ⟨49,by decide⟩).lower ∧ (cell12714 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12714 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12714 ⟨50,by decide⟩).lower ∧ (cell12714 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12714 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12714 ⟨51,by decide⟩).lower ∧ (cell12714 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12714 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12714 ⟨52,by decide⟩).lower ∧ (cell12714 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12714 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12714 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12714 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12714,cell12714,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12714 i).lower ∧
    (cell12714 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12714 i).upper ≤ (0.532 : ℝ) ∧
    (cell12714 i).centre ≤ (0.1 : ℝ) ∧ (cell12714 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12714 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12714 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12714

/-! The local source numeric instances at 12714 have no network premises. -/
namespace BstLean.Part269.N12714
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12714)
open BstLean.Part268 (cell12714)

noncomputable def sourceNumerics12714 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12714 (cell12714 i)
      scalarRow12714.M scalarRow12714.H scalarRow12714.xi := by
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
    energy_allowance := scalarRow12714.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12714]
    centre_nonneg := (scalarRow12714.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12714])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12714
/-! Actual 12715 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12715 ≤ (1.035787906818 : ℝ) := by
  have hr : (112.760808794545 : ℝ) ≤ √(12715 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.760808794545 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12715 12715 (11 / 1000) ≤
    (0.008477121041 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12715) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.760808794545 : ℝ) ≤ √(12715 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12715)
  have hdiv : K / √(12715 : ℝ) ≤ K / 112.760808794545 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.760808794545 ≤ (0.008477121041 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12715.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12715 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12715 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12715 := gPlus_lower 12715
end BstLean.Part269.N12715

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12715
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035787906817 : ℝ) ≤ wn 12715 := by
  have hn : √(12715 : ℝ) ≤ 112.760808794546 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12715 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.760808794546 ≤ 2 / √(12715 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251578546 : ℝ) ≤ rhoBar 12715 BstLean.Part154.csC ∧
    rhoBar 12715 BstLean.Part154.csC ≤ 0.000251578935 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035787906817 : ℝ) / (1.295212 * 12715) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035787906818 : ℝ) / (1.29521 * 12715) := by gcongr
      _ ≤ (0.000251578935 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12715 BstLean.Part154.csC) ≤ 0.001006379032 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12715 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) ≤ 0.000192157677 ∧
    cc1 (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) ≤ 0.000122271208 ∧
    cc2 (rhoBar 12715 BstLean.Part154.csC) ≤ 0.000070979376 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12715 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12715 BstLean.Part154.csC * nuR (rhoBar 12715 BstLean.Part154.csC)) ≤ 0.000503173693 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251578935 : ℝ) * 0.001006379032 := by gcongr
      _ ≤ (0.000503173693 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12715 BstLean.Part154.csC) * nuR (rhoBar 12715 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006379032 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12715 BstLean.Part154.csC) * rhoBar 12715 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251578935 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251578935 / 2 + 0.399 * 0.001006379032 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192157677 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503173693 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122271208 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251578935 / 1.414213562 := by gcongr
      _ ≤ (0.000070979376 : ℝ) := by norm_num

end BstLean.Part269.N12715

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12715
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) ≤ 1.59460E-7 := by
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12715 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12715 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192157677 : ℝ) ^ 2 + 0.000122271208 ^ 2 + 3 * 0.000070979376 ^ 2 +
        2 * 0.797885 * 0.000192157677 * 0.000122271208 + 2 * 0.000192157677 * 0.000070979376 +
        4 * 0.797885 * 0.000122271208 * 0.000070979376 := by gcongr
    _ ≤ (1.59460E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12715 BstLean.Part154.csC Θ ≤ 0.002626086243 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12715 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12715 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035787906818 * 1.59460E-7 / (0.000251578546 : ℝ) := by gcongr
    _ ≤ 0.002626086243 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12715 BstLean.Part154.csC Θ ≤ 0.002913716294 + 0.000663567818 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12715 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035787906818 : ℝ) * ((2 * Θ * 0.000251578935 +
        (6863 / 10000) * 0.000251578935 * 12715 * 0.001006379032) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002913716294 + 0.000663567818 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12715 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12715 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12715 0.011 Θ ∧ gammaRatio 12715 0.011 Θ ≤ 0.000086486333 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12715 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035787906818 : ℝ) * 0.525 / ((1 - 0.011) * 12715) := by gcongr
      _ ≤ (0.000086486333 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12715 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12715 0.011 Θ) :=
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
    badAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12715 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12715 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12715 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12715 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12715 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12715 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12715 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12715 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12715 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12715 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035787906818 : ℝ) * 12715 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003529408771 + 0.003289654061 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12715

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12715
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12715 BstLean.Part154.csC) (piBar (rhoBar 12715 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12715 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12715 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12715 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12715 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12715 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12715 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12715 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12715 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12715 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052453009961 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12715) ≤ 0.010590892296 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12715 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035787906818)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010590892296 + 2 * 0.737676 / 12715) := by gcongr
    _ ≤ (0.052453009961 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12715 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12715

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12715
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504245835 : ℝ) ≤ plow 12715 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12715) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763077154)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378695278) : eMP 12715 0.011 xi bn ≤ 0.001186950948 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12715 : ℝ) * (1 - 0.011))) ≤ 0.000586884685 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378695278 / (12715 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586884685 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586884685 : ℝ) + 3.141593 * 0.052763077154 / (12715 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186950948 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763077154)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378695278) : PiBarMP 12715 12 0.011 xi bn ≤ 0.161155102970 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12715 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037130786122 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.138909393662 : ℝ) ≤ √((12715 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.760808794545 : ℝ) ≤ √(12715 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12715) ≤ 0.123557186329 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037130786122 + 0.052763077154 * 1.772454 / (2 * (112.138909393662 : ℝ))) * (1 + 0.001186950948) +
        8 / (12715 * 112.760808794545) + 0.123557186329 := by gcongr
    _ ≤ (0.161155102970 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763077154)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378695278) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282155158741) :
    parallelOracle 12715 0.011 xi bn cd ≤ 0.162144632354 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12715 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12715 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504245835 : ℝ) ≤ plow 12715 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.760808794545 : ℝ) ≤ √(12715 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282155158741 : ℝ) / (2 * 0.560504245835 * 112.760808794545)) * 0.161155102970 +
        0.282155158741 ^ 2 / (2 * 0.560504245835 * 112.760808794545) := by gcongr
    _ ≤ (0.162144632354 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052763077154) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378695278)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282155158741) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12715 12715 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504245835 : ℝ) ≤ plow 12715 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.760808794545 : ℝ) ≤ √(12715 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12715 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12715 Θ 1.22 ≤ 0.011760296101 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.760808794545 := by gcongr <;> linarith
      _ ≤ (0.011760296101 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12715 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12715 12715 0.011 ≤ 0.008477121041 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12715 12715 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12715 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12715 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12715 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12715 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162144632354 + 0.011760296101 + (0.008477121041 : ℝ) *
        (1 + 2 * (0.282155158741 + 0.011760296101) / (0.560504245835 * 112.760808794545))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12715]

end BstLean.Part269.N12715

/-! The original eight local profiles supply actual 12715 moment certificates. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12715 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052763077154 ∧
    0 ≤ bN 12715 BstLean.Part154.csC (groupTheta g) ∧ bN 12715 BstLean.Part154.csC (groupTheta g) ≤ 0.001378695278 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12715 12715 0.011
      (momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12715 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12715 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12715 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229702148780 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12715 0.011
      (momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12715 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12715
/-! The actual computed-centre upper energy formula at 12715. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12715

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12715)
open BstLean.Part268 (cell12715)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085446633121
  | 2 => 0.086388583681
  | 3 => 0.087328557795
  | 4 => 0.088267946754
  | 5 => 0.089208434277
  | 6 => 0.090152040065
  | 7 => 0.091101167463
  | 8 => 0.092058655296
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12715 12715 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12715 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12715

/-! Actual upper energy certificates on all 43 source endpoints at 12715. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12715)
open BstLean.Part268 (cell12715)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12715 (gMinus 12715) (1 - (cell12715 i).lower) ≤ 1 ∧
    energyUpper 12715 (gMinus 12715) (BstLean.Part211.gPlus 12715)
      (finiteEnergy 12715 12715 0.011) (1 - (cell12715 i).lower) ≤
      (cell12715 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨10,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨11,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨12,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨13,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨14,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨15,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨16,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨17,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨18,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨19,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨20,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨21,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨22,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨23,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨24,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨25,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨26,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨27,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨28,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨29,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨30,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨31,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨32,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨33,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨34,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨35,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨36,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨37,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨38,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨39,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨40,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨41,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨42,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨43,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨44,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨45,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨46,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨47,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨48,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨49,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨50,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨51,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12715) (by norm_num)
        (q := 1 - (cell12715 ⟨52,by decide⟩).lower)
        (by norm_num [cell12715]) (by norm_num [cell12715])
      exact ⟨E.1,E.2.trans (by norm_num [cell12715])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12715

/-! Source-cell containment and simple scalar guards at 12715. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12715)
open BstLean.Part268 (cell12715)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12715 ⟨10,by decide⟩).lower ∧ (cell12715 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12715 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12715 ⟨11,by decide⟩).lower ∧ (cell12715 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12715 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12715 ⟨12,by decide⟩).lower ∧ (cell12715 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12715 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12715 ⟨13,by decide⟩).lower ∧ (cell12715 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12715 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12715 ⟨14,by decide⟩).lower ∧ (cell12715 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12715 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12715 ⟨15,by decide⟩).lower ∧ (cell12715 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12715 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12715 ⟨16,by decide⟩).lower ∧ (cell12715 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12715 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12715 ⟨17,by decide⟩).lower ∧ (cell12715 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12715 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12715 ⟨18,by decide⟩).lower ∧ (cell12715 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12715 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12715 ⟨19,by decide⟩).lower ∧ (cell12715 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12715 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12715 ⟨20,by decide⟩).lower ∧ (cell12715 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12715 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12715 ⟨21,by decide⟩).lower ∧ (cell12715 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12715 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12715 ⟨22,by decide⟩).lower ∧ (cell12715 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12715 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12715 ⟨23,by decide⟩).lower ∧ (cell12715 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12715 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12715 ⟨24,by decide⟩).lower ∧ (cell12715 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12715 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12715 ⟨25,by decide⟩).lower ∧ (cell12715 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12715 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12715 ⟨26,by decide⟩).lower ∧ (cell12715 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12715 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12715 ⟨27,by decide⟩).lower ∧ (cell12715 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12715 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12715 ⟨28,by decide⟩).lower ∧ (cell12715 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12715 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12715 ⟨29,by decide⟩).lower ∧ (cell12715 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12715 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12715 ⟨30,by decide⟩).lower ∧ (cell12715 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12715 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12715 ⟨31,by decide⟩).lower ∧ (cell12715 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12715 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12715 ⟨32,by decide⟩).lower ∧ (cell12715 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12715 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12715 ⟨33,by decide⟩).lower ∧ (cell12715 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12715 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12715 ⟨34,by decide⟩).lower ∧ (cell12715 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12715 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12715 ⟨35,by decide⟩).lower ∧ (cell12715 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12715 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12715 ⟨36,by decide⟩).lower ∧ (cell12715 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12715 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12715 ⟨37,by decide⟩).lower ∧ (cell12715 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12715 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12715 ⟨38,by decide⟩).lower ∧ (cell12715 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12715 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12715 ⟨39,by decide⟩).lower ∧ (cell12715 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12715 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12715 ⟨40,by decide⟩).lower ∧ (cell12715 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12715 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12715 ⟨41,by decide⟩).lower ∧ (cell12715 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12715 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12715 ⟨42,by decide⟩).lower ∧ (cell12715 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12715 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12715 ⟨43,by decide⟩).lower ∧ (cell12715 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12715 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12715 ⟨44,by decide⟩).lower ∧ (cell12715 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12715 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12715 ⟨45,by decide⟩).lower ∧ (cell12715 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12715 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12715 ⟨46,by decide⟩).lower ∧ (cell12715 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12715 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12715 ⟨47,by decide⟩).lower ∧ (cell12715 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12715 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12715 ⟨48,by decide⟩).lower ∧ (cell12715 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12715 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12715 ⟨49,by decide⟩).lower ∧ (cell12715 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12715 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12715 ⟨50,by decide⟩).lower ∧ (cell12715 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12715 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12715 ⟨51,by decide⟩).lower ∧ (cell12715 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12715 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12715 ⟨52,by decide⟩).lower ∧ (cell12715 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12715 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12715 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12715 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12715,cell12715,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12715 i).lower ∧
    (cell12715 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12715 i).upper ≤ (0.532 : ℝ) ∧
    (cell12715 i).centre ≤ (0.1 : ℝ) ∧ (cell12715 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12715 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12715 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12715

/-! The local source numeric instances at 12715 have no network premises. -/
namespace BstLean.Part269.N12715
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12715)
open BstLean.Part268 (cell12715)

noncomputable def sourceNumerics12715 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12715 (cell12715 i)
      scalarRow12715.M scalarRow12715.H scalarRow12715.xi := by
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
    energy_allowance := scalarRow12715.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12715]
    centre_nonneg := (scalarRow12715.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12715])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12715
/-! Actual 12716 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12716 ≤ (1.035786487220 : ℝ) := by
  have hr : (112.765242872083 : ℝ) ≤ √(12716 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.765242872083 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12716 12716 (11 / 1000) ≤
    (0.008476787706 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12716) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.765242872083 : ℝ) ≤ √(12716 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12716)
  have hdiv : K / √(12716 : ℝ) ≤ K / 112.765242872083 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.765242872083 ≤ (0.008476787706 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12716.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12716 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12716 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12716 := gPlus_lower 12716
end BstLean.Part269.N12716

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12716
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035786487219 : ℝ) ≤ wn 12716 := by
  have hn : √(12716 : ℝ) ≤ 112.765242872084 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12716 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.765242872084 ≤ 2 / √(12716 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251558417 : ℝ) ≤ rhoBar 12716 BstLean.Part154.csC ∧
    rhoBar 12716 BstLean.Part154.csC ≤ 0.000251558806 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035786487219 : ℝ) / (1.295212 * 12716) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035786487220 : ℝ) / (1.29521 * 12716) := by gcongr
      _ ≤ (0.000251558806 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12716 BstLean.Part154.csC) ≤ 0.001006298506 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12716 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) ≤ 0.000192142302 ∧
    cc1 (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) ≤ 0.000122261425 ∧
    cc2 (rhoBar 12716 BstLean.Part154.csC) ≤ 0.000070973697 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12716 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12716 BstLean.Part154.csC * nuR (rhoBar 12716 BstLean.Part154.csC)) ≤ 0.000503133433 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251558806 : ℝ) * 0.001006298506 := by gcongr
      _ ≤ (0.000503133433 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12716 BstLean.Part154.csC) * nuR (rhoBar 12716 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006298506 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12716 BstLean.Part154.csC) * rhoBar 12716 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251558806 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251558806 / 2 + 0.399 * 0.001006298506 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192142302 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503133433 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122261425 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251558806 / 1.414213562 := by gcongr
      _ ≤ (0.000070973697 : ℝ) := by norm_num

end BstLean.Part269.N12716

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12716
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) ≤ 1.59434E-7 := by
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12716 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12716 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192142302 : ℝ) ^ 2 + 0.000122261425 ^ 2 + 3 * 0.000070973697 ^ 2 +
        2 * 0.797885 * 0.000192142302 * 0.000122261425 + 2 * 0.000192142302 * 0.000070973697 +
        4 * 0.797885 * 0.000122261425 * 0.000070973697 := by gcongr
    _ ≤ (1.59434E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12716 BstLean.Part154.csC Θ ≤ 0.002625864557 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12716 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12716 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035786487220 * 1.59434E-7 / (0.000251558417 : ℝ) := by gcongr
    _ ≤ 0.002625864557 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12716 BstLean.Part154.csC Θ ≤ 0.002913475167 + 0.000663513816 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12716 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035786487220 : ℝ) * ((2 * Θ * 0.000251558806 +
        (6863 / 10000) * 0.000251558806 * 12716 * 0.001006298506) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002913475167 + 0.000663513816 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12716 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12716 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12716 0.011 Θ ∧ gammaRatio 12716 0.011 Θ ≤ 0.000086479413 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12716 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035786487220 : ℝ) * 0.525 / ((1 - 0.011) * 12716) := by gcongr
      _ ≤ (0.000086479413 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12716 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12716 0.011 Θ) :=
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
    badAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12716 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12716 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12716 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12716 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12716 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12716 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12716 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12716 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12716 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12716 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035786487220 : ℝ) * 12716 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003529167644 + 0.003289378373 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12716

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12716
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12716 BstLean.Part154.csC) (piBar (rhoBar 12716 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12716 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12716 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12716 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12716 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12716 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12716 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12716 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12716 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12716 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052450925088 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12716) ≤ 0.010590475848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12716 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035786487220)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010590475848 + 2 * 0.737676 / 12716) := by gcongr
    _ ≤ (0.052450925088 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12716 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12716

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12716
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504290948 : ℝ) ≤ plow 12716 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12716) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762691290)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378578893) : eMP 12716 0.011 xi bn ≤ 0.001186854119 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12716 : ℝ) * (1 - 0.011))) ≤ 0.000586836837 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378578893 / (12716 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586836837 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586836837 : ℝ) + 3.141593 * 0.052762691290 / (12716 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186854119 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762691290)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378578893) : PiBarMP 12716 12 0.011 xi bn ≤ 0.161148651652 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12716 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037129218858 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.143319016337 : ℝ) ≤ √((12716 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.765242872083 : ℝ) ≤ √(12716 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12716) ≤ 0.123552327898 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037129218858 + 0.052762691290 * 1.772454 / (2 * (112.143319016337 : ℝ))) * (1 + 0.001186854119) +
        8 / (12716 * 112.765242872083) + 0.123552327898 := by gcongr
    _ ≤ (0.161148651652 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762691290)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378578893) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282152233944) :
    parallelOracle 12716 0.011 xi bn cd ≤ 0.162138110862 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12716 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12716 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504290948 : ℝ) ≤ plow 12716 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.765242872083 : ℝ) ≤ √(12716 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282152233944 : ℝ) / (2 * 0.560504290948 * 112.765242872083)) * 0.161148651652 +
        0.282152233944 ^ 2 / (2 * 0.560504290948 * 112.765242872083) := by gcongr
    _ ≤ (0.162138110862 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762691290) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378578893)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282152233944) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12716 12716 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504290948 : ℝ) ≤ plow 12716 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.765242872083 : ℝ) ≤ √(12716 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12716 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12716 Θ 1.22 ≤ 0.011759833671 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.765242872083 := by gcongr <;> linarith
      _ ≤ (0.011759833671 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12716 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12716 12716 0.011 ≤ 0.008476787706 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12716 12716 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12716 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12716 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12716 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12716 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162138110862 + 0.011759833671 + (0.008476787706 : ℝ) *
        (1 + 2 * (0.282152233944 + 0.011759833671) / (0.560504290948 * 112.765242872083))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12716]

end BstLean.Part269.N12716

/-! The original eight local profiles supply actual 12716 moment certificates. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12716 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052762691290 ∧
    0 ≤ bN 12716 BstLean.Part154.csC (groupTheta g) ∧ bN 12716 BstLean.Part154.csC (groupTheta g) ≤ 0.001378578893 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12716 12716 0.011
      (momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12716 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12716 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12716 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229701308856 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12716 0.011
      (momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12716 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12716
/-! The actual computed-centre upper energy formula at 12716. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12716

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12716)
open BstLean.Part268 (cell12716)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085443733497
  | 2 => 0.086385631160
  | 3 => 0.087325544723
  | 4 => 0.088264863707
  | 5 => 0.089205269751
  | 6 => 0.090148780122
  | 7 => 0.091097795340
  | 8 => 0.092055150968
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12716 12716 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12716 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12716

/-! Actual upper energy certificates on all 43 source endpoints at 12716. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12716)
open BstLean.Part268 (cell12716)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12716 (gMinus 12716) (1 - (cell12716 i).lower) ≤ 1 ∧
    energyUpper 12716 (gMinus 12716) (BstLean.Part211.gPlus 12716)
      (finiteEnergy 12716 12716 0.011) (1 - (cell12716 i).lower) ≤
      (cell12716 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨10,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨11,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨12,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨13,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨14,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨15,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨16,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨17,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨18,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨19,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨20,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨21,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨22,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨23,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨24,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨25,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨26,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨27,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨28,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨29,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨30,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨31,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨32,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨33,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨34,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨35,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨36,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨37,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨38,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨39,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨40,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨41,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨42,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨43,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨44,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨45,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨46,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨47,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨48,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨49,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨50,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨51,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12716) (by norm_num)
        (q := 1 - (cell12716 ⟨52,by decide⟩).lower)
        (by norm_num [cell12716]) (by norm_num [cell12716])
      exact ⟨E.1,E.2.trans (by norm_num [cell12716])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12716

/-! Source-cell containment and simple scalar guards at 12716. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12716)
open BstLean.Part268 (cell12716)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12716 ⟨10,by decide⟩).lower ∧ (cell12716 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12716 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12716 ⟨11,by decide⟩).lower ∧ (cell12716 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12716 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12716 ⟨12,by decide⟩).lower ∧ (cell12716 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12716 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12716 ⟨13,by decide⟩).lower ∧ (cell12716 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12716 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12716 ⟨14,by decide⟩).lower ∧ (cell12716 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12716 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12716 ⟨15,by decide⟩).lower ∧ (cell12716 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12716 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12716 ⟨16,by decide⟩).lower ∧ (cell12716 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12716 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12716 ⟨17,by decide⟩).lower ∧ (cell12716 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12716 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12716 ⟨18,by decide⟩).lower ∧ (cell12716 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12716 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12716 ⟨19,by decide⟩).lower ∧ (cell12716 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12716 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12716 ⟨20,by decide⟩).lower ∧ (cell12716 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12716 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12716 ⟨21,by decide⟩).lower ∧ (cell12716 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12716 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12716 ⟨22,by decide⟩).lower ∧ (cell12716 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12716 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12716 ⟨23,by decide⟩).lower ∧ (cell12716 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12716 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12716 ⟨24,by decide⟩).lower ∧ (cell12716 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12716 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12716 ⟨25,by decide⟩).lower ∧ (cell12716 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12716 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12716 ⟨26,by decide⟩).lower ∧ (cell12716 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12716 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12716 ⟨27,by decide⟩).lower ∧ (cell12716 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12716 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12716 ⟨28,by decide⟩).lower ∧ (cell12716 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12716 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12716 ⟨29,by decide⟩).lower ∧ (cell12716 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12716 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12716 ⟨30,by decide⟩).lower ∧ (cell12716 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12716 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12716 ⟨31,by decide⟩).lower ∧ (cell12716 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12716 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12716 ⟨32,by decide⟩).lower ∧ (cell12716 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12716 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12716 ⟨33,by decide⟩).lower ∧ (cell12716 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12716 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12716 ⟨34,by decide⟩).lower ∧ (cell12716 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12716 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12716 ⟨35,by decide⟩).lower ∧ (cell12716 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12716 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12716 ⟨36,by decide⟩).lower ∧ (cell12716 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12716 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12716 ⟨37,by decide⟩).lower ∧ (cell12716 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12716 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12716 ⟨38,by decide⟩).lower ∧ (cell12716 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12716 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12716 ⟨39,by decide⟩).lower ∧ (cell12716 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12716 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12716 ⟨40,by decide⟩).lower ∧ (cell12716 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12716 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12716 ⟨41,by decide⟩).lower ∧ (cell12716 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12716 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12716 ⟨42,by decide⟩).lower ∧ (cell12716 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12716 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12716 ⟨43,by decide⟩).lower ∧ (cell12716 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12716 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12716 ⟨44,by decide⟩).lower ∧ (cell12716 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12716 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12716 ⟨45,by decide⟩).lower ∧ (cell12716 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12716 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12716 ⟨46,by decide⟩).lower ∧ (cell12716 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12716 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12716 ⟨47,by decide⟩).lower ∧ (cell12716 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12716 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12716 ⟨48,by decide⟩).lower ∧ (cell12716 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12716 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12716 ⟨49,by decide⟩).lower ∧ (cell12716 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12716 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12716 ⟨50,by decide⟩).lower ∧ (cell12716 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12716 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12716 ⟨51,by decide⟩).lower ∧ (cell12716 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12716 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12716 ⟨52,by decide⟩).lower ∧ (cell12716 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12716 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12716 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12716 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12716,cell12716,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12716 i).lower ∧
    (cell12716 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12716 i).upper ≤ (0.532 : ℝ) ∧
    (cell12716 i).centre ≤ (0.1 : ℝ) ∧ (cell12716 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12716 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12716 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12716

/-! The local source numeric instances at 12716 have no network premises. -/
namespace BstLean.Part269.N12716
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12716)
open BstLean.Part268 (cell12716)

noncomputable def sourceNumerics12716 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12716 (cell12716 i)
      scalarRow12716.M scalarRow12716.H scalarRow12716.xi := by
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
    energy_allowance := scalarRow12716.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12716]
    centre_nonneg := (scalarRow12716.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12716])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12716
/-! Actual 12717 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12717 ≤ (1.035785067792 : ℝ) := by
  have hr : (112.769676775275 : ℝ) ≤ √(12717 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.769676775275 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12717 12717 (11 / 1000) ≤
    (0.008476454412 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12717) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.769676775275 : ℝ) ≤ √(12717 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12717)
  have hdiv : K / √(12717 : ℝ) ≤ K / 112.769676775275 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.769676775275 ≤ (0.008476454412 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12717.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12717 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12717 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12717 := gPlus_lower 12717
end BstLean.Part269.N12717

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12717
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035785067791 : ℝ) ≤ wn 12717 := by
  have hn : √(12717 : ℝ) ≤ 112.769676775276 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12717 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.769676775276 ≤ 2 / √(12717 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251538291 : ℝ) ≤ rhoBar 12717 BstLean.Part154.csC ∧
    rhoBar 12717 BstLean.Part154.csC ≤ 0.000251538680 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035785067791 : ℝ) / (1.295212 * 12717) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035785067792 : ℝ) / (1.29521 * 12717) := by gcongr
      _ ≤ (0.000251538680 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12717 BstLean.Part154.csC) ≤ 0.001006217992 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12717 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) ≤ 0.000192126929 ∧
    cc1 (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) ≤ 0.000122251643 ∧
    cc2 (rhoBar 12717 BstLean.Part154.csC) ≤ 0.000070968018 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12717 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12717 BstLean.Part154.csC * nuR (rhoBar 12717 BstLean.Part154.csC)) ≤ 0.000503093178 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251538680 : ℝ) * 0.001006217992 := by gcongr
      _ ≤ (0.000503093178 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12717 BstLean.Part154.csC) * nuR (rhoBar 12717 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006217992 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12717 BstLean.Part154.csC) * rhoBar 12717 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251538680 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251538680 / 2 + 0.399 * 0.001006217992 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192126929 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503093178 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122251643 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251538680 / 1.414213562 := by gcongr
      _ ≤ (0.000070968018 : ℝ) := by norm_num

end BstLean.Part269.N12717

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12717
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) ≤ 1.59409E-7 := by
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12717 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12717 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192126929 : ℝ) ^ 2 + 0.000122251643 ^ 2 + 3 * 0.000070968018 ^ 2 +
        2 * 0.797885 * 0.000192126929 * 0.000122251643 + 2 * 0.000192126929 * 0.000070968018 +
        4 * 0.797885 * 0.000122251643 * 0.000070968018 := by gcongr
    _ ≤ (1.59409E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12717 BstLean.Part154.csC Θ ≤ 0.002625659278 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12717 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12717 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035785067792 * 1.59409E-7 / (0.000251538291 : ℝ) := by gcongr
    _ ≤ 0.002625659278 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12717 BstLean.Part154.csC Θ ≤ 0.002913234076 + 0.000663459823 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12717 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035785067792 : ℝ) * ((2 * Θ * 0.000251538680 +
        (6863 / 10000) * 0.000251538680 * 12717 * 0.001006217992) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002913234076 + 0.000663459823 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12717 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12717 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12717 0.011 Θ ∧ gammaRatio 12717 0.011 Θ ≤ 0.000086472494 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12717 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035785067792 : ℝ) * 0.525 / ((1 - 0.011) * 12717) := by gcongr
      _ ≤ (0.000086472494 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12717 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12717 0.011 Θ) :=
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
    badAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12717 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12717 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12717 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12717 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12717 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12717 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12717 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12717 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12717 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12717 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035785067792 : ℝ) * 12717 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003528926553 + 0.003289119101 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12717

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12717
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12717 BstLean.Part154.csC) (piBar (rhoBar 12717 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12717 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12717 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12717 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12717 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12717 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12717 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12717 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12717 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12717 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052448840462 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12717) ≤ 0.010590059449 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12717 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035785067792)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010590059449 + 2 * 0.737676 / 12717) := by gcongr
    _ ≤ (0.052448840462 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12717 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12717

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12717
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504336054 : ℝ) ≤ plow 12717 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12717) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762314082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378471121) : eMP 12717 0.011 xi bn ≤ 0.001186760966 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12717 : ℝ) * (1 - 0.011))) ≤ 0.000586790826 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378471121 / (12717 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586790826 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586790826 : ℝ) + 3.141593 * 0.052762314082 / (12717 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186760966 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762314082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378471121) : PiBarMP 12717 12 0.011 xi bn ≤ 0.161142317180 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12717 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037127767520 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.147728465626 : ℝ) ≤ √((12717 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.769676775275 : ℝ) ≤ √(12717 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12717) ≤ 0.123547470040 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037127767520 + 0.052762314082 * 1.772454 / (2 * (112.147728465626 : ℝ))) * (1 + 0.001186760966) +
        8 / (12717 * 112.769676775275) + 0.123547470040 := by gcongr
    _ ≤ (0.161142317180 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762314082)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378471121) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282149328233) :
    parallelOracle 12717 0.011 xi bn cd ≤ 0.162131706594 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12717 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12717 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504336054 : ℝ) ≤ plow 12717 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.769676775275 : ℝ) ≤ √(12717 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282149328233 : ℝ) / (2 * 0.560504336054 * 112.769676775275)) * 0.161142317180 +
        0.282149328233 ^ 2 / (2 * 0.560504336054 * 112.769676775275) := by gcongr
    _ ≤ (0.162131706594 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052762314082) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378471121)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282149328233) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12717 12717 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504336054 : ℝ) ≤ plow 12717 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.769676775275 : ℝ) ≤ √(12717 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12717 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12717 Θ 1.22 ≤ 0.011759371295 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.769676775275 := by gcongr <;> linarith
      _ ≤ (0.011759371295 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12717 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12717 12717 0.011 ≤ 0.008476454412 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12717 12717 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12717 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12717 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12717 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12717 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162131706594 + 0.011759371295 + (0.008476454412 : ℝ) *
        (1 + 2 * (0.282149328233 + 0.011759371295) / (0.560504336054 * 112.769676775275))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12717]

end BstLean.Part269.N12717

/-! The original eight local profiles supply actual 12717 moment certificates. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12717 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052762314082 ∧
    0 ≤ bN 12717 BstLean.Part154.csC (groupTheta g) ∧ bN 12717 BstLean.Part154.csC (groupTheta g) ≤ 0.001378471121 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12717 12717 0.011
      (momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12717 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12717 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12717 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229700487771 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12717 0.011
      (momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12717 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12717
/-! The actual computed-centre upper energy formula at 12717. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12717

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12717)
open BstLean.Part268 (cell12717)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085440834939
  | 2 => 0.086382679750
  | 3 => 0.087322532815
  | 4 => 0.088261781890
  | 5 => 0.089202106535
  | 6 => 0.090145521588
  | 7 => 0.091094424746
  | 8 => 0.092051648312
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12717 12717 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12717 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12717

/-! Actual upper energy certificates on all 43 source endpoints at 12717. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12717)
open BstLean.Part268 (cell12717)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12717 (gMinus 12717) (1 - (cell12717 i).lower) ≤ 1 ∧
    energyUpper 12717 (gMinus 12717) (BstLean.Part211.gPlus 12717)
      (finiteEnergy 12717 12717 0.011) (1 - (cell12717 i).lower) ≤
      (cell12717 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨10,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨11,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨12,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨13,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨14,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨15,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨16,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨17,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨18,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨19,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨20,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨21,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨22,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨23,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨24,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨25,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨26,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨27,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨28,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨29,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨30,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨31,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨32,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨33,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨34,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨35,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨36,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨37,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨38,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨39,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨40,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨41,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨42,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨43,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨44,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨45,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨46,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨47,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨48,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨49,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨50,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨51,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12717) (by norm_num)
        (q := 1 - (cell12717 ⟨52,by decide⟩).lower)
        (by norm_num [cell12717]) (by norm_num [cell12717])
      exact ⟨E.1,E.2.trans (by norm_num [cell12717])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12717

/-! Source-cell containment and simple scalar guards at 12717. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12717)
open BstLean.Part268 (cell12717)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12717 ⟨10,by decide⟩).lower ∧ (cell12717 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12717 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12717 ⟨11,by decide⟩).lower ∧ (cell12717 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12717 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12717 ⟨12,by decide⟩).lower ∧ (cell12717 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12717 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12717 ⟨13,by decide⟩).lower ∧ (cell12717 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12717 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12717 ⟨14,by decide⟩).lower ∧ (cell12717 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12717 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12717 ⟨15,by decide⟩).lower ∧ (cell12717 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12717 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12717 ⟨16,by decide⟩).lower ∧ (cell12717 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12717 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12717 ⟨17,by decide⟩).lower ∧ (cell12717 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12717 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12717 ⟨18,by decide⟩).lower ∧ (cell12717 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12717 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12717 ⟨19,by decide⟩).lower ∧ (cell12717 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12717 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12717 ⟨20,by decide⟩).lower ∧ (cell12717 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12717 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12717 ⟨21,by decide⟩).lower ∧ (cell12717 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12717 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12717 ⟨22,by decide⟩).lower ∧ (cell12717 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12717 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12717 ⟨23,by decide⟩).lower ∧ (cell12717 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12717 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12717 ⟨24,by decide⟩).lower ∧ (cell12717 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12717 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12717 ⟨25,by decide⟩).lower ∧ (cell12717 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12717 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12717 ⟨26,by decide⟩).lower ∧ (cell12717 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12717 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12717 ⟨27,by decide⟩).lower ∧ (cell12717 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12717 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12717 ⟨28,by decide⟩).lower ∧ (cell12717 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12717 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12717 ⟨29,by decide⟩).lower ∧ (cell12717 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12717 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12717 ⟨30,by decide⟩).lower ∧ (cell12717 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12717 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12717 ⟨31,by decide⟩).lower ∧ (cell12717 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12717 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12717 ⟨32,by decide⟩).lower ∧ (cell12717 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12717 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12717 ⟨33,by decide⟩).lower ∧ (cell12717 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12717 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12717 ⟨34,by decide⟩).lower ∧ (cell12717 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12717 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12717 ⟨35,by decide⟩).lower ∧ (cell12717 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12717 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12717 ⟨36,by decide⟩).lower ∧ (cell12717 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12717 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12717 ⟨37,by decide⟩).lower ∧ (cell12717 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12717 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12717 ⟨38,by decide⟩).lower ∧ (cell12717 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12717 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12717 ⟨39,by decide⟩).lower ∧ (cell12717 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12717 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12717 ⟨40,by decide⟩).lower ∧ (cell12717 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12717 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12717 ⟨41,by decide⟩).lower ∧ (cell12717 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12717 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12717 ⟨42,by decide⟩).lower ∧ (cell12717 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12717 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12717 ⟨43,by decide⟩).lower ∧ (cell12717 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12717 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12717 ⟨44,by decide⟩).lower ∧ (cell12717 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12717 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12717 ⟨45,by decide⟩).lower ∧ (cell12717 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12717 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12717 ⟨46,by decide⟩).lower ∧ (cell12717 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12717 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12717 ⟨47,by decide⟩).lower ∧ (cell12717 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12717 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12717 ⟨48,by decide⟩).lower ∧ (cell12717 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12717 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12717 ⟨49,by decide⟩).lower ∧ (cell12717 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12717 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12717 ⟨50,by decide⟩).lower ∧ (cell12717 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12717 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12717 ⟨51,by decide⟩).lower ∧ (cell12717 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12717 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12717 ⟨52,by decide⟩).lower ∧ (cell12717 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12717 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12717 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12717 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12717,cell12717,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12717 i).lower ∧
    (cell12717 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12717 i).upper ≤ (0.532 : ℝ) ∧
    (cell12717 i).centre ≤ (0.1 : ℝ) ∧ (cell12717 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12717 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12717 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12717

/-! The local source numeric instances at 12717 have no network premises. -/
namespace BstLean.Part269.N12717
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12717)
open BstLean.Part268 (cell12717)

noncomputable def sourceNumerics12717 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12717 (cell12717 i)
      scalarRow12717.M scalarRow12717.H scalarRow12717.xi := by
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
    energy_allowance := scalarRow12717.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12717]
    centre_nonneg := (scalarRow12717.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12717])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12717
/-! Actual 12718 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12718 ≤ (1.035783648531 : ℝ) := by
  have hr : (112.774110504140 : ℝ) ≤ √(12718 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.774110504140 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12718 12718 (11 / 1000) ≤
    (0.008476121156 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12718) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.774110504140 : ℝ) ≤ √(12718 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12718)
  have hdiv : K / √(12718 : ℝ) ≤ K / 112.774110504140 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.774110504140 ≤ (0.008476121156 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12718.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12718 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12718 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12718 := gPlus_lower 12718
end BstLean.Part269.N12718

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12718
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035783648530 : ℝ) ≤ wn 12718 := by
  have hn : √(12718 : ℝ) ≤ 112.774110504141 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12718 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.774110504141 ≤ 2 / √(12718 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251518168 : ℝ) ≤ rhoBar 12718 BstLean.Part154.csC ∧
    rhoBar 12718 BstLean.Part154.csC ≤ 0.000251518557 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035783648530 : ℝ) / (1.295212 * 12718) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035783648531 : ℝ) / (1.29521 * 12718) := by gcongr
      _ ≤ (0.000251518557 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12718 BstLean.Part154.csC) ≤ 0.001006137490 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12718 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) ≤ 0.000192111558 ∧
    cc1 (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) ≤ 0.000122241862 ∧
    cc2 (rhoBar 12718 BstLean.Part154.csC) ≤ 0.000070962341 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12718 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12718 BstLean.Part154.csC * nuR (rhoBar 12718 BstLean.Part154.csC)) ≤ 0.000503052930 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251518557 : ℝ) * 0.001006137490 := by gcongr
      _ ≤ (0.000503052930 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12718 BstLean.Part154.csC) * nuR (rhoBar 12718 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006137490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12718 BstLean.Part154.csC) * rhoBar 12718 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251518557 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251518557 / 2 + 0.399 * 0.001006137490 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192111558 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503052930 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122241862 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251518557 / 1.414213562 := by gcongr
      _ ≤ (0.000070962341 : ℝ) := by norm_num

end BstLean.Part269.N12718

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12718
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) ≤ 1.59383E-7 := by
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12718 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12718 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192111558 : ℝ) ^ 2 + 0.000122241862 ^ 2 + 3 * 0.000070962341 ^ 2 +
        2 * 0.797885 * 0.000192111558 * 0.000122241862 + 2 * 0.000192111558 * 0.000070962341 +
        4 * 0.797885 * 0.000122241862 * 0.000070962341 := by gcongr
    _ ≤ (1.59383E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12718 BstLean.Part154.csC Θ ≤ 0.002625437464 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12718 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12718 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035783648531 * 1.59383E-7 / (0.000251518168 : ℝ) := by gcongr
    _ ≤ 0.002625437464 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12718 BstLean.Part154.csC Θ ≤ 0.002912993018 + 0.000663405837 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12718 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035783648531 : ℝ) * ((2 * Θ * 0.000251518557 +
        (6863 / 10000) * 0.000251518557 * 12718 * 0.001006137490) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002912993018 + 0.000663405837 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12718 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12718 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12718 0.011 Θ ∧ gammaRatio 12718 0.011 Θ ≤ 0.000086465576 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12718 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035783648531 : ℝ) * 0.525 / ((1 - 0.011) * 12718) := by gcongr
      _ ≤ (0.000086465576 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12718 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12718 0.011 Θ) :=
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
    badAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12718 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12718 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12718 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12718 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12718 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12718 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12718 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12718 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12718 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12718 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035783648531 : ℝ) * 12718 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003528685495 + 0.003288843301 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12718

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12718
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12718 BstLean.Part154.csC) (piBar (rhoBar 12718 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12718 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12718 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12718 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12718 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12718 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12718 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12718 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12718 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12718 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052446756087 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12718) ≤ 0.010589643100 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12718 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035783648531)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010589643100 + 2 * 0.737676 / 12718) := by gcongr
    _ ≤ (0.052446756087 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12718 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12718

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12718
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504381152 : ℝ) ≤ plow 12718 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12718) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761928229)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378354669) : eMP 12718 0.011 xi bn ≤ 0.001186664123 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12718 : ℝ) * (1 - 0.011))) ≤ 0.000586742971 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378354669 / (12718 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586742971 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586742971 : ℝ) + 3.141593 * 0.052761928229 / (12718 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186664123 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761928229)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378354669) : PiBarMP 12718 12 0.011 xi bn ≤ 0.161135865983 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12718 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037126199227 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.152137741551 : ℝ) ≤ √((12718 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.774110504140 : ℝ) ≤ √(12718 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12718) ≤ 0.123542612755 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037126199227 + 0.052761928229 * 1.772454 / (2 * (112.152137741551 : ℝ))) * (1 + 0.001186664123) +
        8 / (12718 * 112.774110504140) + 0.123542612755 := by gcongr
    _ ≤ (0.161135865983 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761928229)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378354669) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282146403952) :
    parallelOracle 12718 0.011 xi bn cd ≤ 0.162125185241 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12718 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12718 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504381152 : ℝ) ≤ plow 12718 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.774110504140 : ℝ) ≤ √(12718 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282146403952 : ℝ) / (2 * 0.560504381152 * 112.774110504140)) * 0.161135865983 +
        0.282146403952 ^ 2 / (2 * 0.560504381152 * 112.774110504140) := by gcongr
    _ ≤ (0.162125185241 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761928229) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378354669)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282146403952) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12718 12718 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504381152 : ℝ) ≤ plow 12718 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.774110504140 : ℝ) ≤ √(12718 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12718 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12718 Θ 1.22 ≤ 0.011758908974 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.774110504140 := by gcongr <;> linarith
      _ ≤ (0.011758908974 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12718 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12718 12718 0.011 ≤ 0.008476121156 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12718 12718 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12718 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12718 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12718 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12718 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162125185241 + 0.011758908974 + (0.008476121156 : ℝ) *
        (1 + 2 * (0.282146403952 + 0.011758908974) / (0.560504381152 * 112.774110504140))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12718]

end BstLean.Part269.N12718

/-! The original eight local profiles supply actual 12718 moment certificates. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12718 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052761928229 ∧
    0 ≤ bN 12718 BstLean.Part154.csC (groupTheta g) ∧ bN 12718 BstLean.Part154.csC (groupTheta g) ≤ 0.001378354669 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12718 12718 0.011
      (momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12718 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12718 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12718 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229699647865 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12718 0.011
      (momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12718 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12718
/-! The actual computed-centre upper energy formula at 12718. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12718

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12718)
open BstLean.Part268 (cell12718)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085437937446
  | 2 => 0.086379729449
  | 3 => 0.087319522070
  | 4 => 0.088258701301
  | 5 => 0.089198944629
  | 6 => 0.090142264461
  | 7 => 0.091091055678
  | 8 => 0.092048147326
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12718 12718 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12718 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12718

/-! Actual upper energy certificates on all 43 source endpoints at 12718. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12718)
open BstLean.Part268 (cell12718)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12718 (gMinus 12718) (1 - (cell12718 i).lower) ≤ 1 ∧
    energyUpper 12718 (gMinus 12718) (BstLean.Part211.gPlus 12718)
      (finiteEnergy 12718 12718 0.011) (1 - (cell12718 i).lower) ≤
      (cell12718 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨10,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨11,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨12,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨13,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨14,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨15,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨16,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨17,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨18,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨19,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨20,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨21,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨22,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨23,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨24,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨25,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨26,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨27,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨28,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨29,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨30,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨31,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨32,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨33,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨34,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨35,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨36,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨37,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨38,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨39,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨40,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨41,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨42,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨43,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨44,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨45,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨46,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨47,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨48,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨49,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨50,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨51,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12718) (by norm_num)
        (q := 1 - (cell12718 ⟨52,by decide⟩).lower)
        (by norm_num [cell12718]) (by norm_num [cell12718])
      exact ⟨E.1,E.2.trans (by norm_num [cell12718])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12718

/-! Source-cell containment and simple scalar guards at 12718. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12718)
open BstLean.Part268 (cell12718)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12718 ⟨10,by decide⟩).lower ∧ (cell12718 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12718 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12718 ⟨11,by decide⟩).lower ∧ (cell12718 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12718 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12718 ⟨12,by decide⟩).lower ∧ (cell12718 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12718 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12718 ⟨13,by decide⟩).lower ∧ (cell12718 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12718 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12718 ⟨14,by decide⟩).lower ∧ (cell12718 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12718 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12718 ⟨15,by decide⟩).lower ∧ (cell12718 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12718 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12718 ⟨16,by decide⟩).lower ∧ (cell12718 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12718 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12718 ⟨17,by decide⟩).lower ∧ (cell12718 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12718 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12718 ⟨18,by decide⟩).lower ∧ (cell12718 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12718 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12718 ⟨19,by decide⟩).lower ∧ (cell12718 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12718 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12718 ⟨20,by decide⟩).lower ∧ (cell12718 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12718 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12718 ⟨21,by decide⟩).lower ∧ (cell12718 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12718 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12718 ⟨22,by decide⟩).lower ∧ (cell12718 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12718 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12718 ⟨23,by decide⟩).lower ∧ (cell12718 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12718 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12718 ⟨24,by decide⟩).lower ∧ (cell12718 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12718 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12718 ⟨25,by decide⟩).lower ∧ (cell12718 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12718 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12718 ⟨26,by decide⟩).lower ∧ (cell12718 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12718 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12718 ⟨27,by decide⟩).lower ∧ (cell12718 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12718 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12718 ⟨28,by decide⟩).lower ∧ (cell12718 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12718 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12718 ⟨29,by decide⟩).lower ∧ (cell12718 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12718 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12718 ⟨30,by decide⟩).lower ∧ (cell12718 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12718 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12718 ⟨31,by decide⟩).lower ∧ (cell12718 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12718 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12718 ⟨32,by decide⟩).lower ∧ (cell12718 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12718 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12718 ⟨33,by decide⟩).lower ∧ (cell12718 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12718 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12718 ⟨34,by decide⟩).lower ∧ (cell12718 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12718 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12718 ⟨35,by decide⟩).lower ∧ (cell12718 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12718 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12718 ⟨36,by decide⟩).lower ∧ (cell12718 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12718 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12718 ⟨37,by decide⟩).lower ∧ (cell12718 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12718 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12718 ⟨38,by decide⟩).lower ∧ (cell12718 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12718 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12718 ⟨39,by decide⟩).lower ∧ (cell12718 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12718 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12718 ⟨40,by decide⟩).lower ∧ (cell12718 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12718 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12718 ⟨41,by decide⟩).lower ∧ (cell12718 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12718 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12718 ⟨42,by decide⟩).lower ∧ (cell12718 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12718 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12718 ⟨43,by decide⟩).lower ∧ (cell12718 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12718 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12718 ⟨44,by decide⟩).lower ∧ (cell12718 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12718 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12718 ⟨45,by decide⟩).lower ∧ (cell12718 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12718 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12718 ⟨46,by decide⟩).lower ∧ (cell12718 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12718 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12718 ⟨47,by decide⟩).lower ∧ (cell12718 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12718 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12718 ⟨48,by decide⟩).lower ∧ (cell12718 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12718 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12718 ⟨49,by decide⟩).lower ∧ (cell12718 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12718 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12718 ⟨50,by decide⟩).lower ∧ (cell12718 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12718 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12718 ⟨51,by decide⟩).lower ∧ (cell12718 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12718 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12718 ⟨52,by decide⟩).lower ∧ (cell12718 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12718 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12718 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12718 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12718,cell12718,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12718 i).lower ∧
    (cell12718 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12718 i).upper ≤ (0.532 : ℝ) ∧
    (cell12718 i).centre ≤ (0.1 : ℝ) ∧ (cell12718 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12718 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12718 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12718

/-! The local source numeric instances at 12718 have no network premises. -/
namespace BstLean.Part269.N12718
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12718)
open BstLean.Part268 (cell12718)

noncomputable def sourceNumerics12718 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12718 (cell12718 i)
      scalarRow12718.M scalarRow12718.H scalarRow12718.xi := by
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
    energy_allowance := scalarRow12718.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12718]
    centre_nonneg := (scalarRow12718.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12718])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12718
/-! Actual 12719 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12719 ≤ (1.035782229440 : ℝ) := by
  have hr : (112.778544058699 : ℝ) ≤ √(12719 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.778544058699 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12719 12719 (11 / 1000) ≤
    (0.008475787940 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12719) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.778544058699 : ℝ) ≤ √(12719 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12719)
  have hdiv : K / √(12719 : ℝ) ≤ K / 112.778544058699 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.778544058699 ≤ (0.008475787940 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12719.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12719 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12719 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12719 := gPlus_lower 12719
end BstLean.Part269.N12719

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12719
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035782229439 : ℝ) ≤ wn 12719 := by
  have hn : √(12719 : ℝ) ≤ 112.778544058700 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12719 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.778544058700 ≤ 2 / √(12719 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251498048 : ℝ) ≤ rhoBar 12719 BstLean.Part154.csC ∧
    rhoBar 12719 BstLean.Part154.csC ≤ 0.000251498438 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035782229439 : ℝ) / (1.295212 * 12719) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035782229440 : ℝ) / (1.29521 * 12719) := by gcongr
      _ ≤ (0.000251498438 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12719 BstLean.Part154.csC) ≤ 0.001006057004 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12719 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) ≤ 0.000192096190 ∧
    cc1 (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) ≤ 0.000122232084 ∧
    cc2 (rhoBar 12719 BstLean.Part154.csC) ≤ 0.000070956665 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12719 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12719 BstLean.Part154.csC * nuR (rhoBar 12719 BstLean.Part154.csC)) ≤ 0.000503012689 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251498438 : ℝ) * 0.001006057004 := by gcongr
      _ ≤ (0.000503012689 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12719 BstLean.Part154.csC) * nuR (rhoBar 12719 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006057004 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12719 BstLean.Part154.csC) * rhoBar 12719 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251498438 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251498438 / 2 + 0.399 * 0.001006057004 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192096190 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503012689 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122232084 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251498438 / 1.414213562 := by gcongr
      _ ≤ (0.000070956665 : ℝ) := by norm_num

end BstLean.Part269.N12719

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12719
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) ≤ 1.59358E-7 := by
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12719 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12719 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192096190 : ℝ) ^ 2 + 0.000122232084 ^ 2 + 3 * 0.000070956665 ^ 2 +
        2 * 0.797885 * 0.000192096190 * 0.000122232084 + 2 * 0.000192096190 * 0.000070956665 +
        4 * 0.797885 * 0.000122232084 * 0.000070956665 := by gcongr
    _ ≤ (1.59358E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12719 BstLean.Part154.csC Θ ≤ 0.002625232058 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12719 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12719 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035782229440 * 1.59358E-7 / (0.000251498048 : ℝ) := by gcongr
    _ ≤ 0.002625232058 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12719 BstLean.Part154.csC Θ ≤ 0.002912752019 + 0.000663351862 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12719 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035782229440 : ℝ) * ((2 * Θ * 0.000251498438 +
        (6863 / 10000) * 0.000251498438 * 12719 * 0.001006057004) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002912752019 + 0.000663351862 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12719 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12719 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12719 0.011 Θ ∧ gammaRatio 12719 0.011 Θ ≤ 0.000086458660 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12719 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035782229440 : ℝ) * 0.525 / ((1 - 0.011) * 12719) := by gcongr
      _ ≤ (0.000086458660 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12719 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12719 0.011 Θ) :=
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
    badAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12719 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12719 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12719 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12719 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12719 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12719 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12719 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12719 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12719 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12719 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035782229440 : ℝ) * 12719 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003528444496 + 0.003288583920 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12719

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12719
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12719 BstLean.Part154.csC) (piBar (rhoBar 12719 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12719 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12719 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12719 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12719 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12719 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12719 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12719 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12719 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12719 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052444671955 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12719) ≤ 0.010589226799 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12719 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035782229440)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010589226799 + 2 * 0.737676 / 12719) := by gcongr
    _ ≤ (0.052444671955 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12719 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12719

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12719
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504426244 : ℝ) ≤ plow 12719 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12719) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761551054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378246831) : eMP 12719 0.011 xi bn ≤ 0.001186570957 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12719 : ℝ) * (1 - 0.011))) ≤ 0.000586696953 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378246831 / (12719 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586696953 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586696953 : ℝ) + 3.141593 * 0.052761551054 / (12719 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186570957 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761551054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378246831) : PiBarMP 12719 12 0.011 xi bn ≤ 0.161129531654 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12719 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037124746882 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.156546844132 : ℝ) ≤ √((12719 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.778544058699 : ℝ) ≤ √(12719 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12719) ≤ 0.123537756043 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037124746882 + 0.052761551054 * 1.772454 / (2 * (112.156546844132 : ℝ))) * (1 + 0.001186570957) +
        8 / (12719 * 112.778544058699) + 0.123537756043 := by gcongr
    _ ≤ (0.161129531654 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761551054)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378246831) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282143498801) :
    parallelOracle 12719 0.011 xi bn cd ≤ 0.162118781134 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12719 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12719 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504426244 : ℝ) ≤ plow 12719 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.778544058699 : ℝ) ≤ √(12719 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282143498801 : ℝ) / (2 * 0.560504426244 * 112.778544058699)) * 0.161129531654 +
        0.282143498801 ^ 2 / (2 * 0.560504426244 * 112.778544058699) := by gcongr
    _ ≤ (0.162118781134 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761551054) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378246831)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282143498801) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12719 12719 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504426244 : ℝ) ≤ plow 12719 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.778544058699 : ℝ) ≤ √(12719 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12719 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12719 Θ 1.22 ≤ 0.011758446707 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.778544058699 := by gcongr <;> linarith
      _ ≤ (0.011758446707 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12719 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12719 12719 0.011 ≤ 0.008475787940 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12719 12719 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12719 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12719 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12719 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12719 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162118781134 + 0.011758446707 + (0.008475787940 : ℝ) *
        (1 + 2 * (0.282143498801 + 0.011758446707) / (0.560504426244 * 112.778544058699))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12719]

end BstLean.Part269.N12719

/-! The original eight local profiles supply actual 12719 moment certificates. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12719 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052761551054 ∧
    0 ≤ bN 12719 BstLean.Part154.csC (groupTheta g) ∧ bN 12719 BstLean.Part154.csC (groupTheta g) ≤ 0.001378246831 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12719 12719 0.011
      (momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12719 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12719 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12719 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229698826846 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12719 0.011
      (momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12719 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12719
/-! The actual computed-centre upper energy formula at 12719. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12719

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12719)
open BstLean.Part268 (cell12719)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085435041018
  | 2 => 0.086376780255
  | 3 => 0.087316512486
  | 4 => 0.088255621941
  | 5 => 0.089195784031
  | 6 => 0.090139008741
  | 7 => 0.091087688135
  | 8 => 0.092044648008
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12719 12719 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12719 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12719

/-! Actual upper energy certificates on all 43 source endpoints at 12719. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12719)
open BstLean.Part268 (cell12719)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12719 (gMinus 12719) (1 - (cell12719 i).lower) ≤ 1 ∧
    energyUpper 12719 (gMinus 12719) (BstLean.Part211.gPlus 12719)
      (finiteEnergy 12719 12719 0.011) (1 - (cell12719 i).lower) ≤
      (cell12719 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨10,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨11,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨12,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨13,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨14,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨15,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨16,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨17,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨18,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨19,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨20,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨21,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨22,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨23,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨24,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨25,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨26,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨27,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨28,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨29,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨30,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨31,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨32,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨33,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨34,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨35,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨36,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨37,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨38,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨39,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨40,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨41,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨42,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨43,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨44,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨45,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨46,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨47,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨48,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨49,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨50,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨51,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12719) (by norm_num)
        (q := 1 - (cell12719 ⟨52,by decide⟩).lower)
        (by norm_num [cell12719]) (by norm_num [cell12719])
      exact ⟨E.1,E.2.trans (by norm_num [cell12719])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12719

/-! Source-cell containment and simple scalar guards at 12719. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12719)
open BstLean.Part268 (cell12719)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12719 ⟨10,by decide⟩).lower ∧ (cell12719 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12719 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12719 ⟨11,by decide⟩).lower ∧ (cell12719 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12719 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12719 ⟨12,by decide⟩).lower ∧ (cell12719 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12719 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12719 ⟨13,by decide⟩).lower ∧ (cell12719 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12719 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12719 ⟨14,by decide⟩).lower ∧ (cell12719 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12719 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12719 ⟨15,by decide⟩).lower ∧ (cell12719 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12719 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12719 ⟨16,by decide⟩).lower ∧ (cell12719 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12719 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12719 ⟨17,by decide⟩).lower ∧ (cell12719 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12719 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12719 ⟨18,by decide⟩).lower ∧ (cell12719 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12719 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12719 ⟨19,by decide⟩).lower ∧ (cell12719 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12719 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12719 ⟨20,by decide⟩).lower ∧ (cell12719 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12719 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12719 ⟨21,by decide⟩).lower ∧ (cell12719 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12719 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12719 ⟨22,by decide⟩).lower ∧ (cell12719 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12719 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12719 ⟨23,by decide⟩).lower ∧ (cell12719 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12719 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12719 ⟨24,by decide⟩).lower ∧ (cell12719 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12719 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12719 ⟨25,by decide⟩).lower ∧ (cell12719 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12719 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12719 ⟨26,by decide⟩).lower ∧ (cell12719 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12719 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12719 ⟨27,by decide⟩).lower ∧ (cell12719 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12719 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12719 ⟨28,by decide⟩).lower ∧ (cell12719 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12719 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12719 ⟨29,by decide⟩).lower ∧ (cell12719 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12719 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12719 ⟨30,by decide⟩).lower ∧ (cell12719 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12719 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12719 ⟨31,by decide⟩).lower ∧ (cell12719 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12719 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12719 ⟨32,by decide⟩).lower ∧ (cell12719 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12719 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12719 ⟨33,by decide⟩).lower ∧ (cell12719 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12719 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12719 ⟨34,by decide⟩).lower ∧ (cell12719 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12719 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12719 ⟨35,by decide⟩).lower ∧ (cell12719 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12719 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12719 ⟨36,by decide⟩).lower ∧ (cell12719 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12719 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12719 ⟨37,by decide⟩).lower ∧ (cell12719 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12719 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12719 ⟨38,by decide⟩).lower ∧ (cell12719 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12719 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12719 ⟨39,by decide⟩).lower ∧ (cell12719 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12719 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12719 ⟨40,by decide⟩).lower ∧ (cell12719 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12719 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12719 ⟨41,by decide⟩).lower ∧ (cell12719 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12719 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12719 ⟨42,by decide⟩).lower ∧ (cell12719 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12719 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12719 ⟨43,by decide⟩).lower ∧ (cell12719 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12719 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12719 ⟨44,by decide⟩).lower ∧ (cell12719 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12719 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12719 ⟨45,by decide⟩).lower ∧ (cell12719 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12719 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12719 ⟨46,by decide⟩).lower ∧ (cell12719 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12719 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12719 ⟨47,by decide⟩).lower ∧ (cell12719 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12719 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12719 ⟨48,by decide⟩).lower ∧ (cell12719 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12719 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12719 ⟨49,by decide⟩).lower ∧ (cell12719 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12719 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12719 ⟨50,by decide⟩).lower ∧ (cell12719 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12719 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12719 ⟨51,by decide⟩).lower ∧ (cell12719 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12719 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12719 ⟨52,by decide⟩).lower ∧ (cell12719 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12719 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12719 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12719 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12719,cell12719,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12719 i).lower ∧
    (cell12719 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12719 i).upper ≤ (0.532 : ℝ) ∧
    (cell12719 i).centre ≤ (0.1 : ℝ) ∧ (cell12719 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12719 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12719 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12719

/-! The local source numeric instances at 12719 have no network premises. -/
namespace BstLean.Part269.N12719
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12719)
open BstLean.Part268 (cell12719)

noncomputable def sourceNumerics12719 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12719 (cell12719 i)
      scalarRow12719.M scalarRow12719.H scalarRow12719.xi := by
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
    energy_allowance := scalarRow12719.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12719]
    centre_nonneg := (scalarRow12719.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12719])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12719
/-! Actual 12720 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12720 ≤ (1.035780810516 : ℝ) := by
  have hr : (112.782977438973 : ℝ) ≤ √(12720 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.782977438973 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12720 12720 (11 / 1000) ≤
    (0.008475454763 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12720) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.782977438973 : ℝ) ≤ √(12720 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12720)
  have hdiv : K / √(12720 : ℝ) ≤ K / 112.782977438973 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.782977438973 ≤ (0.008475454763 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12720.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12720 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12720 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12720 := gPlus_lower 12720
end BstLean.Part269.N12720

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12720
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035780810515 : ℝ) ≤ wn 12720 := by
  have hn : √(12720 : ℝ) ≤ 112.782977438974 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12720 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.782977438974 ≤ 2 / √(12720 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251477932 : ℝ) ≤ rhoBar 12720 BstLean.Part154.csC ∧
    rhoBar 12720 BstLean.Part154.csC ≤ 0.000251478321 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035780810515 : ℝ) / (1.295212 * 12720) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035780810516 : ℝ) / (1.29521 * 12720) := by gcongr
      _ ≤ (0.000251478321 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12720 BstLean.Part154.csC) ≤ 0.001005976526 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12720 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) ≤ 0.000192080824 ∧
    cc1 (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) ≤ 0.000122222307 ∧
    cc2 (rhoBar 12720 BstLean.Part154.csC) ≤ 0.000070950989 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12720 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12720 BstLean.Part154.csC * nuR (rhoBar 12720 BstLean.Part154.csC)) ≤ 0.000502972453 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251478321 : ℝ) * 0.001005976526 := by gcongr
      _ ≤ (0.000502972453 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12720 BstLean.Part154.csC) * nuR (rhoBar 12720 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005976526 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12720 BstLean.Part154.csC) * rhoBar 12720 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251478321 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251478321 / 2 + 0.399 * 0.001005976526 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192080824 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502972453 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122222307 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251478321 / 1.414213562 := by gcongr
      _ ≤ (0.000070950989 : ℝ) := by norm_num

end BstLean.Part269.N12720

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12720
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) ≤ 1.59332E-7 := by
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12720 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12720 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192080824 : ℝ) ^ 2 + 0.000122222307 ^ 2 + 3 * 0.000070950989 ^ 2 +
        2 * 0.797885 * 0.000192080824 * 0.000122222307 + 2 * 0.000192080824 * 0.000070950989 +
        4 * 0.797885 * 0.000122222307 * 0.000070950989 := by gcongr
    _ ≤ (1.59332E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12720 BstLean.Part154.csC Θ ≤ 0.002625010104 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12720 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12720 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035780810516 * 1.59332E-7 / (0.000251477932 : ℝ) := by gcongr
    _ ≤ 0.002625010104 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12720 BstLean.Part154.csC Θ ≤ 0.002912511031 + 0.000663297893 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12720 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035780810516 : ℝ) * ((2 * Θ * 0.000251478321 +
        (6863 / 10000) * 0.000251478321 * 12720 * 0.001005976526) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002912511031 + 0.000663297893 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12720 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12720 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12720 0.011 Θ ∧ gammaRatio 12720 0.011 Θ ≤ 0.000086451744 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12720 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035780810516 : ℝ) * 0.525 / ((1 - 0.011) * 12720) := by gcongr
      _ ≤ (0.000086451744 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12720 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12720 0.011 Θ) :=
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
    badAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12720 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12720 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12720 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12720 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12720 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12720 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12720 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12720 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12720 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12720 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035780810516 : ℝ) * 12720 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003528203508 + 0.003288307997 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12720

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12720
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12720 BstLean.Part154.csC) (piBar (rhoBar 12720 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12720 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12720 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12720 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12720 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12720 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12720 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12720 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12720 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12720 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052442588075 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12720) ≤ 0.010588810548 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12720 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035780810516)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010588810548 + 2 * 0.737676 / 12720) := by gcongr
    _ ≤ (0.052442588075 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12720 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12720

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12720
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504471328 : ℝ) ≤ plow 12720 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12720) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761165207)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378130305) : eMP 12720 0.011 xi bn ≤ 0.001186474097 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12720 : ℝ) * (1 - 0.011))) ≤ 0.000586649089 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378130305 / (12720 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586649089 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586649089 : ℝ) + 3.141593 * 0.052761165207 / (12720 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186474097 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761165207)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378130305) : PiBarMP 12720 12 0.011 xi bn ≤ 0.161123080481 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12720 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037123177464 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.160955773388 : ℝ) ≤ √((12720 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.782977438973 : ℝ) ≤ √(12720 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12720) ≤ 0.123532899904 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037123177464 + 0.052761165207 * 1.772454 / (2 * (112.160955773388 : ℝ))) * (1 + 0.001186474097) +
        8 / (12720 * 112.782977438973) + 0.123532899904 := by gcongr
    _ ≤ (0.161123080481 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761165207)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378130305) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282140575021) :
    parallelOracle 12720 0.011 xi bn cd ≤ 0.162112259824 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12720 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12720 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504471328 : ℝ) ≤ plow 12720 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.782977438973 : ℝ) ≤ √(12720 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282140575021 : ℝ) / (2 * 0.560504471328 * 112.782977438973)) * 0.161123080481 +
        0.282140575021 ^ 2 / (2 * 0.560504471328 * 112.782977438973) := by gcongr
    _ ≤ (0.162112259824 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052761165207) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378130305)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282140575021) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12720 12720 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504471328 : ℝ) ≤ plow 12720 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.782977438973 : ℝ) ≤ √(12720 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12720 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12720 Θ 1.22 ≤ 0.011757984495 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.782977438973 := by gcongr <;> linarith
      _ ≤ (0.011757984495 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12720 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12720 12720 0.011 ≤ 0.008475454763 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12720 12720 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12720 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12720 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12720 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12720 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162112259824 + 0.011757984495 + (0.008475454763 : ℝ) *
        (1 + 2 * (0.282140575021 + 0.011757984495) / (0.560504471328 * 112.782977438973))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12720]

end BstLean.Part269.N12720

/-! The original eight local profiles supply actual 12720 moment certificates. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12720 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052761165207 ∧
    0 ≤ bN 12720 BstLean.Part154.csC (groupTheta g) ∧ bN 12720 BstLean.Part154.csC (groupTheta g) ≤ 0.001378130305 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12720 12720 0.011
      (momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12720 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12720 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12720 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229697986946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12720 0.011
      (momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12720 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12720
/-! The actual computed-centre upper energy formula at 12720. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12720

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12720)
open BstLean.Part268 (cell12720)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085432145654
  | 2 => 0.086373832169
  | 3 => 0.087313504063
  | 4 => 0.088252543806
  | 5 => 0.089192624740
  | 6 => 0.090135754426
  | 7 => 0.091084322116
  | 8 => 0.092041150356
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12720 12720 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12720 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12720

/-! Actual upper energy certificates on all 43 source endpoints at 12720. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12720)
open BstLean.Part268 (cell12720)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12720 (gMinus 12720) (1 - (cell12720 i).lower) ≤ 1 ∧
    energyUpper 12720 (gMinus 12720) (BstLean.Part211.gPlus 12720)
      (finiteEnergy 12720 12720 0.011) (1 - (cell12720 i).lower) ≤
      (cell12720 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨10,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨11,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨12,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨13,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨14,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨15,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨16,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨17,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨18,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨19,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨20,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨21,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨22,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨23,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨24,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨25,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨26,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨27,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨28,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨29,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨30,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨31,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨32,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨33,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨34,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨35,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨36,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨37,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨38,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨39,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨40,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨41,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨42,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨43,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨44,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨45,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨46,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨47,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨48,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨49,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨50,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨51,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12720) (by norm_num)
        (q := 1 - (cell12720 ⟨52,by decide⟩).lower)
        (by norm_num [cell12720]) (by norm_num [cell12720])
      exact ⟨E.1,E.2.trans (by norm_num [cell12720])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12720

/-! Source-cell containment and simple scalar guards at 12720. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12720)
open BstLean.Part268 (cell12720)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12720 ⟨10,by decide⟩).lower ∧ (cell12720 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12720 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12720 ⟨11,by decide⟩).lower ∧ (cell12720 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12720 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12720 ⟨12,by decide⟩).lower ∧ (cell12720 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12720 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12720 ⟨13,by decide⟩).lower ∧ (cell12720 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12720 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12720 ⟨14,by decide⟩).lower ∧ (cell12720 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12720 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12720 ⟨15,by decide⟩).lower ∧ (cell12720 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12720 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12720 ⟨16,by decide⟩).lower ∧ (cell12720 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12720 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12720 ⟨17,by decide⟩).lower ∧ (cell12720 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12720 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12720 ⟨18,by decide⟩).lower ∧ (cell12720 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12720 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12720 ⟨19,by decide⟩).lower ∧ (cell12720 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12720 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12720 ⟨20,by decide⟩).lower ∧ (cell12720 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12720 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12720 ⟨21,by decide⟩).lower ∧ (cell12720 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12720 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12720 ⟨22,by decide⟩).lower ∧ (cell12720 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12720 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12720 ⟨23,by decide⟩).lower ∧ (cell12720 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12720 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12720 ⟨24,by decide⟩).lower ∧ (cell12720 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12720 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12720 ⟨25,by decide⟩).lower ∧ (cell12720 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12720 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12720 ⟨26,by decide⟩).lower ∧ (cell12720 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12720 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12720 ⟨27,by decide⟩).lower ∧ (cell12720 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12720 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12720 ⟨28,by decide⟩).lower ∧ (cell12720 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12720 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12720 ⟨29,by decide⟩).lower ∧ (cell12720 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12720 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12720 ⟨30,by decide⟩).lower ∧ (cell12720 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12720 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12720 ⟨31,by decide⟩).lower ∧ (cell12720 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12720 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12720 ⟨32,by decide⟩).lower ∧ (cell12720 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12720 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12720 ⟨33,by decide⟩).lower ∧ (cell12720 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12720 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12720 ⟨34,by decide⟩).lower ∧ (cell12720 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12720 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12720 ⟨35,by decide⟩).lower ∧ (cell12720 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12720 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12720 ⟨36,by decide⟩).lower ∧ (cell12720 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12720 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12720 ⟨37,by decide⟩).lower ∧ (cell12720 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12720 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12720 ⟨38,by decide⟩).lower ∧ (cell12720 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12720 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12720 ⟨39,by decide⟩).lower ∧ (cell12720 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12720 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12720 ⟨40,by decide⟩).lower ∧ (cell12720 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12720 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12720 ⟨41,by decide⟩).lower ∧ (cell12720 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12720 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12720 ⟨42,by decide⟩).lower ∧ (cell12720 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12720 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12720 ⟨43,by decide⟩).lower ∧ (cell12720 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12720 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12720 ⟨44,by decide⟩).lower ∧ (cell12720 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12720 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12720 ⟨45,by decide⟩).lower ∧ (cell12720 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12720 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12720 ⟨46,by decide⟩).lower ∧ (cell12720 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12720 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12720 ⟨47,by decide⟩).lower ∧ (cell12720 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12720 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12720 ⟨48,by decide⟩).lower ∧ (cell12720 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12720 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12720 ⟨49,by decide⟩).lower ∧ (cell12720 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12720 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12720 ⟨50,by decide⟩).lower ∧ (cell12720 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12720 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12720 ⟨51,by decide⟩).lower ∧ (cell12720 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12720 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12720 ⟨52,by decide⟩).lower ∧ (cell12720 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12720 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12720 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12720 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12720,cell12720,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12720 i).lower ∧
    (cell12720 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12720 i).upper ≤ (0.532 : ℝ) ∧
    (cell12720 i).centre ≤ (0.1 : ℝ) ∧ (cell12720 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12720 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12720 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12720

/-! The local source numeric instances at 12720 have no network premises. -/
namespace BstLean.Part269.N12720
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12720)
open BstLean.Part268 (cell12720)

noncomputable def sourceNumerics12720 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12720 (cell12720 i)
      scalarRow12720.M scalarRow12720.H scalarRow12720.xi := by
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
    energy_allowance := scalarRow12720.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12720]
    centre_nonneg := (scalarRow12720.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12720])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12720
/-! Actual 12721 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12721 ≤ (1.035779391761 : ℝ) := by
  have hr : (112.787410644982 : ℝ) ≤ √(12721 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.787410644982 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12721 12721 (11 / 1000) ≤
    (0.008475121626 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12721) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.787410644982 : ℝ) ≤ √(12721 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12721)
  have hdiv : K / √(12721 : ℝ) ≤ K / 112.787410644982 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.787410644982 ≤ (0.008475121626 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12721.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12721 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12721 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12721 := gPlus_lower 12721
end BstLean.Part269.N12721

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12721
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035779391760 : ℝ) ≤ wn 12721 := by
  have hn : √(12721 : ℝ) ≤ 112.787410644983 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12721 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.787410644983 ≤ 2 / √(12721 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251457819 : ℝ) ≤ rhoBar 12721 BstLean.Part154.csC ∧
    rhoBar 12721 BstLean.Part154.csC ≤ 0.000251458208 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035779391760 : ℝ) / (1.295212 * 12721) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035779391761 : ℝ) / (1.29521 * 12721) := by gcongr
      _ ≤ (0.000251458208 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12721 BstLean.Part154.csC) ≤ 0.001005896064 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12721 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) ≤ 0.000192065461 ∧
    cc1 (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) ≤ 0.000122212531 ∧
    cc2 (rhoBar 12721 BstLean.Part154.csC) ≤ 0.000070945314 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12721 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12721 BstLean.Part154.csC * nuR (rhoBar 12721 BstLean.Part154.csC)) ≤ 0.000502932224 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251458208 : ℝ) * 0.001005896064 := by gcongr
      _ ≤ (0.000502932224 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12721 BstLean.Part154.csC) * nuR (rhoBar 12721 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005896064 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12721 BstLean.Part154.csC) * rhoBar 12721 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251458208 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251458208 / 2 + 0.399 * 0.001005896064 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192065461 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502932224 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122212531 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251458208 / 1.414213562 := by gcongr
      _ ≤ (0.000070945314 : ℝ) := by norm_num

end BstLean.Part269.N12721

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12721
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) ≤ 1.59307E-7 := by
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12721 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12721 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192065461 : ℝ) ^ 2 + 0.000122212531 ^ 2 + 3 * 0.000070945314 ^ 2 +
        2 * 0.797885 * 0.000192065461 * 0.000122212531 + 2 * 0.000192065461 * 0.000070945314 +
        4 * 0.797885 * 0.000122212531 * 0.000070945314 := by gcongr
    _ ≤ (1.59307E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12721 BstLean.Part154.csC Θ ≤ 0.002624804562 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12721 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12721 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035779391761 * 1.59307E-7 / (0.000251457819 : ℝ) := by gcongr
    _ ≤ 0.002624804562 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12721 BstLean.Part154.csC Θ ≤ 0.002912270101 + 0.000663243935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12721 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035779391761 : ℝ) * ((2 * Θ * 0.000251458208 +
        (6863 / 10000) * 0.000251458208 * 12721 * 0.001005896064) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002912270101 + 0.000663243935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12721 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12721 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12721 0.011 Θ ∧ gammaRatio 12721 0.011 Θ ≤ 0.000086444830 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12721 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035779391761 : ℝ) * 0.525 / ((1 - 0.011) * 12721) := by gcongr
      _ ≤ (0.000086444830 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12721 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12721 0.011 Θ) :=
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
    badAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12721 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12721 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12721 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12721 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12721 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12721 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12721 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12721 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12721 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12721 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035779391761 : ℝ) * 12721 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003527962578 + 0.003288048497 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12721

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12721
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12721 BstLean.Part154.csC) (piBar (rhoBar 12721 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12721 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12721 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12721 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12721 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12721 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12721 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12721 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12721 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12721 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052440504438 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12721) ≤ 0.010588394345 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12721 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035779391761)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010588394345 + 2 * 0.737676 / 12721) := by gcongr
    _ ≤ (0.052440504438 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12721 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12721

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12721
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504516405 : ℝ) ≤ plow 12721 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12721) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760788039)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378022396) : eMP 12721 0.011 xi bn ≤ 0.001186380915 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12721 : ℝ) * (1 - 0.011))) ≤ 0.000586603063 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001378022396 / (12721 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586603063 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586603063 : ℝ) + 3.141593 * 0.052760788039 / (12721 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186380915 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760788039)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378022396) : PiBarMP 12721 12 0.011 xi bn ≤ 0.161116746226 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12721 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037121724045 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.165364529341 : ℝ) ≤ √((12721 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.787410644982 : ℝ) ≤ √(12721 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12721) ≤ 0.123528044337 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037121724045 + 0.052760788039 * 1.772454 / (2 * (112.165364529341 : ℝ))) * (1 + 0.001186380915) +
        8 / (12721 * 112.787410644982) + 0.123528044337 := by gcongr
    _ ≤ (0.161116746226 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760788039)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378022396) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282137670374) :
    parallelOracle 12721 0.011 xi bn cd ≤ 0.162105855809 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12721 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12721 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504516405 : ℝ) ≤ plow 12721 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.787410644982 : ℝ) ≤ √(12721 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282137670374 : ℝ) / (2 * 0.560504516405 * 112.787410644982)) * 0.161116746226 +
        0.282137670374 ^ 2 / (2 * 0.560504516405 * 112.787410644982) := by gcongr
    _ ≤ (0.162105855809 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760788039) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001378022396)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282137670374) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12721 12721 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504516405 : ℝ) ≤ plow 12721 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.787410644982 : ℝ) ≤ √(12721 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12721 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12721 Θ 1.22 ≤ 0.011757522338 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.787410644982 := by gcongr <;> linarith
      _ ≤ (0.011757522338 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12721 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12721 12721 0.011 ≤ 0.008475121626 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12721 12721 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12721 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12721 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12721 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12721 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162105855809 + 0.011757522338 + (0.008475121626 : ℝ) *
        (1 + 2 * (0.282137670374 + 0.011757522338) / (0.560504516405 * 112.787410644982))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12721]

end BstLean.Part269.N12721

/-! The original eight local profiles supply actual 12721 moment certificates. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12721 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052760788039 ∧
    0 ≤ bN 12721 BstLean.Part154.csC (groupTheta g) ∧ bN 12721 BstLean.Part154.csC (groupTheta g) ≤ 0.001378022396 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12721 12721 0.011
      (momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12721 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12721 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12721 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229697165936 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12721 0.011
      (momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12721 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12721
/-! The actual computed-centre upper energy formula at 12721. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12721

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12721)
open BstLean.Part268 (cell12721)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085429251351
  | 2 => 0.086370885188
  | 3 => 0.087310496798
  | 4 => 0.088249466897
  | 5 => 0.089189466754
  | 6 => 0.090132501515
  | 7 => 0.091080957618
  | 8 => 0.092037654368
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12721 12721 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12721 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12721

/-! Actual upper energy certificates on all 43 source endpoints at 12721. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12721)
open BstLean.Part268 (cell12721)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12721 (gMinus 12721) (1 - (cell12721 i).lower) ≤ 1 ∧
    energyUpper 12721 (gMinus 12721) (BstLean.Part211.gPlus 12721)
      (finiteEnergy 12721 12721 0.011) (1 - (cell12721 i).lower) ≤
      (cell12721 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨10,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨11,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨12,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨13,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨14,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨15,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨16,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨17,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨18,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨19,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨20,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨21,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨22,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨23,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨24,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨25,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨26,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨27,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨28,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨29,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨30,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨31,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨32,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨33,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨34,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨35,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨36,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨37,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨38,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨39,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨40,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨41,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨42,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨43,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨44,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨45,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨46,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨47,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨48,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨49,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨50,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨51,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12721) (by norm_num)
        (q := 1 - (cell12721 ⟨52,by decide⟩).lower)
        (by norm_num [cell12721]) (by norm_num [cell12721])
      exact ⟨E.1,E.2.trans (by norm_num [cell12721])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12721

/-! Source-cell containment and simple scalar guards at 12721. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12721)
open BstLean.Part268 (cell12721)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12721 ⟨10,by decide⟩).lower ∧ (cell12721 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12721 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12721 ⟨11,by decide⟩).lower ∧ (cell12721 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12721 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12721 ⟨12,by decide⟩).lower ∧ (cell12721 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12721 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12721 ⟨13,by decide⟩).lower ∧ (cell12721 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12721 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12721 ⟨14,by decide⟩).lower ∧ (cell12721 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12721 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12721 ⟨15,by decide⟩).lower ∧ (cell12721 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12721 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12721 ⟨16,by decide⟩).lower ∧ (cell12721 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12721 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12721 ⟨17,by decide⟩).lower ∧ (cell12721 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12721 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12721 ⟨18,by decide⟩).lower ∧ (cell12721 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12721 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12721 ⟨19,by decide⟩).lower ∧ (cell12721 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12721 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12721 ⟨20,by decide⟩).lower ∧ (cell12721 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12721 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12721 ⟨21,by decide⟩).lower ∧ (cell12721 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12721 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12721 ⟨22,by decide⟩).lower ∧ (cell12721 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12721 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12721 ⟨23,by decide⟩).lower ∧ (cell12721 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12721 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12721 ⟨24,by decide⟩).lower ∧ (cell12721 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12721 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12721 ⟨25,by decide⟩).lower ∧ (cell12721 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12721 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12721 ⟨26,by decide⟩).lower ∧ (cell12721 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12721 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12721 ⟨27,by decide⟩).lower ∧ (cell12721 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12721 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12721 ⟨28,by decide⟩).lower ∧ (cell12721 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12721 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12721 ⟨29,by decide⟩).lower ∧ (cell12721 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12721 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12721 ⟨30,by decide⟩).lower ∧ (cell12721 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12721 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12721 ⟨31,by decide⟩).lower ∧ (cell12721 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12721 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12721 ⟨32,by decide⟩).lower ∧ (cell12721 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12721 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12721 ⟨33,by decide⟩).lower ∧ (cell12721 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12721 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12721 ⟨34,by decide⟩).lower ∧ (cell12721 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12721 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12721 ⟨35,by decide⟩).lower ∧ (cell12721 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12721 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12721 ⟨36,by decide⟩).lower ∧ (cell12721 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12721 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12721 ⟨37,by decide⟩).lower ∧ (cell12721 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12721 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12721 ⟨38,by decide⟩).lower ∧ (cell12721 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12721 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12721 ⟨39,by decide⟩).lower ∧ (cell12721 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12721 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12721 ⟨40,by decide⟩).lower ∧ (cell12721 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12721 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12721 ⟨41,by decide⟩).lower ∧ (cell12721 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12721 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12721 ⟨42,by decide⟩).lower ∧ (cell12721 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12721 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12721 ⟨43,by decide⟩).lower ∧ (cell12721 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12721 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12721 ⟨44,by decide⟩).lower ∧ (cell12721 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12721 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12721 ⟨45,by decide⟩).lower ∧ (cell12721 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12721 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12721 ⟨46,by decide⟩).lower ∧ (cell12721 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12721 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12721 ⟨47,by decide⟩).lower ∧ (cell12721 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12721 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12721 ⟨48,by decide⟩).lower ∧ (cell12721 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12721 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12721 ⟨49,by decide⟩).lower ∧ (cell12721 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12721 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12721 ⟨50,by decide⟩).lower ∧ (cell12721 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12721 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12721 ⟨51,by decide⟩).lower ∧ (cell12721 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12721 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12721 ⟨52,by decide⟩).lower ∧ (cell12721 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12721 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12721 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12721 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12721,cell12721,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12721 i).lower ∧
    (cell12721 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12721 i).upper ≤ (0.532 : ℝ) ∧
    (cell12721 i).centre ≤ (0.1 : ℝ) ∧ (cell12721 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12721 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12721 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12721

/-! The local source numeric instances at 12721 have no network premises. -/
namespace BstLean.Part269.N12721
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12721)
open BstLean.Part268 (cell12721)

noncomputable def sourceNumerics12721 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12721 (cell12721 i)
      scalarRow12721.M scalarRow12721.H scalarRow12721.xi := by
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
    energy_allowance := scalarRow12721.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12721]
    centre_nonneg := (scalarRow12721.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12721])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12721
/-! Actual 12722 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12722 ≤ (1.035777973174 : ℝ) := by
  have hr : (112.791843676748 : ℝ) ≤ √(12722 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.791843676748 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12722 12722 (11 / 1000) ≤
    (0.008474788527 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12722) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.791843676748 : ℝ) ≤ √(12722 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12722)
  have hdiv : K / √(12722 : ℝ) ≤ K / 112.791843676748 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.791843676748 ≤ (0.008474788527 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12722.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12722 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12722 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12722 := gPlus_lower 12722
end BstLean.Part269.N12722

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12722
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035777973173 : ℝ) ≤ wn 12722 := by
  have hn : √(12722 : ℝ) ≤ 112.791843676749 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12722 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.791843676749 ≤ 2 / √(12722 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251437709 : ℝ) ≤ rhoBar 12722 BstLean.Part154.csC ∧
    rhoBar 12722 BstLean.Part154.csC ≤ 0.000251438098 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035777973173 : ℝ) / (1.295212 * 12722) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035777973174 : ℝ) / (1.29521 * 12722) := by gcongr
      _ ≤ (0.000251438098 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12722 BstLean.Part154.csC) ≤ 0.001005815614 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12722 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) ≤ 0.000192050100 ∧
    cc1 (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) ≤ 0.000122202757 ∧
    cc2 (rhoBar 12722 BstLean.Part154.csC) ≤ 0.000070939641 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12722 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12722 BstLean.Part154.csC * nuR (rhoBar 12722 BstLean.Part154.csC)) ≤ 0.000502892002 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251438098 : ℝ) * 0.001005815614 := by gcongr
      _ ≤ (0.000502892002 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12722 BstLean.Part154.csC) * nuR (rhoBar 12722 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005815614 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12722 BstLean.Part154.csC) * rhoBar 12722 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251438098 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251438098 / 2 + 0.399 * 0.001005815614 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192050100 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502892002 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122202757 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251438098 / 1.414213562 := by gcongr
      _ ≤ (0.000070939641 : ℝ) := by norm_num

end BstLean.Part269.N12722

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12722
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) ≤ 1.59281E-7 := by
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12722 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12722 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192050100 : ℝ) ^ 2 + 0.000122202757 ^ 2 + 3 * 0.000070939641 ^ 2 +
        2 * 0.797885 * 0.000192050100 * 0.000122202757 + 2 * 0.000192050100 * 0.000070939641 +
        4 * 0.797885 * 0.000122202757 * 0.000070939641 := by gcongr
    _ ≤ (1.59281E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12722 BstLean.Part154.csC Θ ≤ 0.002624582479 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12722 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12722 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035777973174 * 1.59281E-7 / (0.000251437709 : ℝ) := by gcongr
    _ ≤ 0.002624582479 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12722 BstLean.Part154.csC Θ ≤ 0.002912029205 + 0.000663189984 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12722 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035777973174 : ℝ) * ((2 * Θ * 0.000251438098 +
        (6863 / 10000) * 0.000251438098 * 12722 * 0.001005815614) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002912029205 + 0.000663189984 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12722 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12722 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12722 0.011 Θ ∧ gammaRatio 12722 0.011 Θ ≤ 0.000086437916 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12722 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035777973174 : ℝ) * 0.525 / ((1 - 0.011) * 12722) := by gcongr
      _ ≤ (0.000086437916 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12722 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12722 0.011 Θ) :=
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
    badAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12722 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12722 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12722 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12722 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12722 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12722 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12722 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12722 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12722 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12722 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035777973174 : ℝ) * 12722 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003527721682 + 0.003287772463 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12722

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12722
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12722 BstLean.Part154.csC) (piBar (rhoBar 12722 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12722 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12722 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12722 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12722 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12722 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12722 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12722 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12722 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12722 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052438421052 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12722) ≤ 0.010587978192 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12722 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035777973174)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010587978192 + 2 * 0.737676 / 12722) := by gcongr
    _ ≤ (0.052438421052 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12722 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12722

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12722
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504561476 : ℝ) ≤ plow 12722 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12722) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760402226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377905802) : eMP 12722 0.011 xi bn ≤ 0.001186284041 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12722 : ℝ) * (1 - 0.011))) ≤ 0.000586555192 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377905802 / (12722 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586555192 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586555192 : ℝ) + 3.141593 * 0.052760402226 / (12722 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186284041 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760402226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377905802) : PiBarMP 12722 12 0.011 xi bn ≤ 0.161110295157 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12722 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037120153583 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.169773112010 : ℝ) ≤ √((12722 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.791843676748 : ℝ) ≤ √(12722 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12722) ≤ 0.123523189343 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037120153583 + 0.052760402226 * 1.772454 / (2 * (112.169773112010 : ℝ))) * (1 + 0.001186284041) +
        8 / (12722 * 112.791843676748) + 0.123523189343 := by gcongr
    _ ≤ (0.161110295157 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760402226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377905802) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282134747157) :
    parallelOracle 12722 0.011 xi bn cd ≤ 0.162099334621 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12722 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12722 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504561476 : ℝ) ≤ plow 12722 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.791843676748 : ℝ) ≤ √(12722 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282134747157 : ℝ) / (2 * 0.560504561476 * 112.791843676748)) * 0.161110295157 +
        0.282134747157 ^ 2 / (2 * 0.560504561476 * 112.791843676748) := by gcongr
    _ ≤ (0.162099334621 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760402226) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377905802)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282134747157) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12722 12722 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504561476 : ℝ) ≤ plow 12722 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.791843676748 : ℝ) ≤ √(12722 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12722 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12722 Θ 1.22 ≤ 0.011757060234 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.791843676748 := by gcongr <;> linarith
      _ ≤ (0.011757060234 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12722 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12722 12722 0.011 ≤ 0.008474788527 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12722 12722 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12722 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12722 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12722 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12722 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162099334621 + 0.011757060234 + (0.008474788527 : ℝ) *
        (1 + 2 * (0.282134747157 + 0.011757060234) / (0.560504561476 * 112.791843676748))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12722]

end BstLean.Part269.N12722

/-! The original eight local profiles supply actual 12722 moment certificates. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12722 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052760402226 ∧
    0 ≤ bN 12722 BstLean.Part154.csC (groupTheta g) ∧ bN 12722 BstLean.Part154.csC (groupTheta g) ≤ 0.001377905802 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12722 12722 0.011
      (momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12722 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12722 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12722 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229696326105 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12722 0.011
      (momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12722 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12722
/-! The actual computed-centre upper energy formula at 12722. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12722

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12722)
open BstLean.Part268 (cell12722)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085426358110
  | 2 => 0.086367939311
  | 3 => 0.087307490692
  | 4 => 0.088246391211
  | 5 => 0.089186310072
  | 6 => 0.090129250005
  | 7 => 0.091077594641
  | 8 => 0.092034160042
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12722 12722 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12722 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12722

/-! Actual upper energy certificates on all 43 source endpoints at 12722. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12722)
open BstLean.Part268 (cell12722)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12722 (gMinus 12722) (1 - (cell12722 i).lower) ≤ 1 ∧
    energyUpper 12722 (gMinus 12722) (BstLean.Part211.gPlus 12722)
      (finiteEnergy 12722 12722 0.011) (1 - (cell12722 i).lower) ≤
      (cell12722 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨10,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨11,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨12,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨13,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨14,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨15,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨16,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨17,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨18,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨19,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨20,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨21,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨22,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨23,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨24,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨25,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨26,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨27,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨28,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨29,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨30,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨31,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨32,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨33,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨34,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨35,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨36,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨37,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨38,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨39,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨40,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨41,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨42,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨43,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨44,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨45,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨46,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨47,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨48,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨49,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨50,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨51,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12722) (by norm_num)
        (q := 1 - (cell12722 ⟨52,by decide⟩).lower)
        (by norm_num [cell12722]) (by norm_num [cell12722])
      exact ⟨E.1,E.2.trans (by norm_num [cell12722])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12722

/-! Source-cell containment and simple scalar guards at 12722. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12722)
open BstLean.Part268 (cell12722)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12722 ⟨10,by decide⟩).lower ∧ (cell12722 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12722 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12722 ⟨11,by decide⟩).lower ∧ (cell12722 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12722 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12722 ⟨12,by decide⟩).lower ∧ (cell12722 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12722 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12722 ⟨13,by decide⟩).lower ∧ (cell12722 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12722 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12722 ⟨14,by decide⟩).lower ∧ (cell12722 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12722 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12722 ⟨15,by decide⟩).lower ∧ (cell12722 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12722 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12722 ⟨16,by decide⟩).lower ∧ (cell12722 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12722 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12722 ⟨17,by decide⟩).lower ∧ (cell12722 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12722 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12722 ⟨18,by decide⟩).lower ∧ (cell12722 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12722 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12722 ⟨19,by decide⟩).lower ∧ (cell12722 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12722 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12722 ⟨20,by decide⟩).lower ∧ (cell12722 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12722 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12722 ⟨21,by decide⟩).lower ∧ (cell12722 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12722 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12722 ⟨22,by decide⟩).lower ∧ (cell12722 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12722 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12722 ⟨23,by decide⟩).lower ∧ (cell12722 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12722 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12722 ⟨24,by decide⟩).lower ∧ (cell12722 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12722 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12722 ⟨25,by decide⟩).lower ∧ (cell12722 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12722 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12722 ⟨26,by decide⟩).lower ∧ (cell12722 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12722 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12722 ⟨27,by decide⟩).lower ∧ (cell12722 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12722 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12722 ⟨28,by decide⟩).lower ∧ (cell12722 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12722 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12722 ⟨29,by decide⟩).lower ∧ (cell12722 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12722 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12722 ⟨30,by decide⟩).lower ∧ (cell12722 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12722 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12722 ⟨31,by decide⟩).lower ∧ (cell12722 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12722 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12722 ⟨32,by decide⟩).lower ∧ (cell12722 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12722 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12722 ⟨33,by decide⟩).lower ∧ (cell12722 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12722 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12722 ⟨34,by decide⟩).lower ∧ (cell12722 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12722 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12722 ⟨35,by decide⟩).lower ∧ (cell12722 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12722 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12722 ⟨36,by decide⟩).lower ∧ (cell12722 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12722 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12722 ⟨37,by decide⟩).lower ∧ (cell12722 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12722 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12722 ⟨38,by decide⟩).lower ∧ (cell12722 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12722 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12722 ⟨39,by decide⟩).lower ∧ (cell12722 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12722 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12722 ⟨40,by decide⟩).lower ∧ (cell12722 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12722 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12722 ⟨41,by decide⟩).lower ∧ (cell12722 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12722 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12722 ⟨42,by decide⟩).lower ∧ (cell12722 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12722 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12722 ⟨43,by decide⟩).lower ∧ (cell12722 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12722 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12722 ⟨44,by decide⟩).lower ∧ (cell12722 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12722 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12722 ⟨45,by decide⟩).lower ∧ (cell12722 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12722 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12722 ⟨46,by decide⟩).lower ∧ (cell12722 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12722 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12722 ⟨47,by decide⟩).lower ∧ (cell12722 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12722 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12722 ⟨48,by decide⟩).lower ∧ (cell12722 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12722 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12722 ⟨49,by decide⟩).lower ∧ (cell12722 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12722 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12722 ⟨50,by decide⟩).lower ∧ (cell12722 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12722 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12722 ⟨51,by decide⟩).lower ∧ (cell12722 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12722 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12722 ⟨52,by decide⟩).lower ∧ (cell12722 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12722 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12722 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12722 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12722,cell12722,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12722 i).lower ∧
    (cell12722 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12722 i).upper ≤ (0.532 : ℝ) ∧
    (cell12722 i).centre ≤ (0.1 : ℝ) ∧ (cell12722 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12722 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12722 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12722

/-! The local source numeric instances at 12722 have no network premises. -/
namespace BstLean.Part269.N12722
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12722)
open BstLean.Part268 (cell12722)

noncomputable def sourceNumerics12722 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12722 (cell12722 i)
      scalarRow12722.M scalarRow12722.H scalarRow12722.xi := by
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
    energy_allowance := scalarRow12722.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12722]
    centre_nonneg := (scalarRow12722.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12722])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12722
/-! Actual 12723 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12723 ≤ (1.035776554755 : ℝ) := by
  have hr : (112.796276534289 : ℝ) ≤ √(12723 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.796276534289 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12723 12723 (11 / 1000) ≤
    (0.008474455468 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12723) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.796276534289 : ℝ) ≤ √(12723 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12723)
  have hdiv : K / √(12723 : ℝ) ≤ K / 112.796276534289 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.796276534289 ≤ (0.008474455468 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12723.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12723 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12723 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12723 := gPlus_lower 12723
end BstLean.Part269.N12723

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12723
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035776554754 : ℝ) ≤ wn 12723 := by
  have hn : √(12723 : ℝ) ≤ 112.796276534290 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12723 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.796276534290 ≤ 2 / √(12723 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251417602 : ℝ) ≤ rhoBar 12723 BstLean.Part154.csC ∧
    rhoBar 12723 BstLean.Part154.csC ≤ 0.000251417991 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035776554754 : ℝ) / (1.295212 * 12723) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035776554755 : ℝ) / (1.29521 * 12723) := by gcongr
      _ ≤ (0.000251417991 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12723 BstLean.Part154.csC) ≤ 0.001005735176 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12723 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) ≤ 0.000192034741 ∧
    cc1 (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) ≤ 0.000122192984 ∧
    cc2 (rhoBar 12723 BstLean.Part154.csC) ≤ 0.000070933968 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12723 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12723 BstLean.Part154.csC * nuR (rhoBar 12723 BstLean.Part154.csC)) ≤ 0.000502851785 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251417991 : ℝ) * 0.001005735176 := by gcongr
      _ ≤ (0.000502851785 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12723 BstLean.Part154.csC) * nuR (rhoBar 12723 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005735176 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12723 BstLean.Part154.csC) * rhoBar 12723 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251417991 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251417991 / 2 + 0.399 * 0.001005735176 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192034741 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502851785 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122192984 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251417991 / 1.414213562 := by gcongr
      _ ≤ (0.000070933968 : ℝ) := by norm_num

end BstLean.Part269.N12723

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12723
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) ≤ 1.59256E-7 := by
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12723 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12723 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192034741 : ℝ) ^ 2 + 0.000122192984 ^ 2 + 3 * 0.000070933968 ^ 2 +
        2 * 0.797885 * 0.000192034741 * 0.000122192984 + 2 * 0.000192034741 * 0.000070933968 +
        4 * 0.797885 * 0.000122192984 * 0.000070933968 := by gcongr
    _ ≤ (1.59256E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12723 BstLean.Part154.csC Θ ≤ 0.002624376809 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12723 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12723 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035776554755 * 1.59256E-7 / (0.000251417602 : ℝ) := by gcongr
    _ ≤ 0.002624376809 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12723 BstLean.Part154.csC Θ ≤ 0.002911788344 + 0.000663136042 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12723 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035776554755 : ℝ) * ((2 * Θ * 0.000251417991 +
        (6863 / 10000) * 0.000251417991 * 12723 * 0.001005735176) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002911788344 + 0.000663136042 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12723 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12723 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12723 0.011 Θ ∧ gammaRatio 12723 0.011 Θ ≤ 0.000086431004 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12723 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035776554755 : ℝ) * 0.525 / ((1 - 0.011) * 12723) := by gcongr
      _ ≤ (0.000086431004 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12723 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12723 0.011 Θ) :=
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
    badAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12723 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12723 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12723 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12723 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12723 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12723 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12723 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12723 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12723 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12723 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035776554755 : ℝ) * 12723 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003527480821 + 0.003287512851 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12723

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12723
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12723 BstLean.Part154.csC) (piBar (rhoBar 12723 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12723 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12723 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12723 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12723 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12723 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12723 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12723 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12723 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12723 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052436337913 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12723) ≤ 0.010587562088 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12723 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035776554755)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010587562088 + 2 * 0.737676 / 12723) := by gcongr
    _ ≤ (0.052436337913 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12723 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12723

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12723
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504606539 : ℝ) ≤ plow 12723 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12723) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760025068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377797825) : eMP 12723 0.011 xi bn ≤ 0.001186190845 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12723 : ℝ) * (1 - 0.011))) ≤ 0.000586509159 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377797825 / (12723 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586509159 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586509159 : ℝ) + 3.141593 * 0.052760025068 / (12723 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186190845 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760025068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377797825) : PiBarMP 12723 12 0.011 xi bn ≤ 0.161103961016 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12723 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037118699129 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.174181521417 : ℝ) ≤ √((12723 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.796276534289 : ℝ) ≤ √(12723 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12723) ≤ 0.123518334921 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037118699129 + 0.052760025068 * 1.772454 / (2 * (112.174181521417 : ℝ))) * (1 + 0.001186190845) +
        8 / (12723 * 112.796276534289) + 0.123518334921 := by gcongr
    _ ≤ (0.161103961016 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760025068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377797825) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282131843024) :
    parallelOracle 12723 0.011 xi bn cd ≤ 0.162092930738 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12723 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12723 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504606539 : ℝ) ≤ plow 12723 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.796276534289 : ℝ) ≤ √(12723 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282131843024 : ℝ) / (2 * 0.560504606539 * 112.796276534289)) * 0.161103961016 +
        0.282131843024 ^ 2 / (2 * 0.560504606539 * 112.796276534289) := by gcongr
    _ ≤ (0.162092930738 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052760025068) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377797825)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282131843024) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12723 12723 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504606539 : ℝ) ≤ plow 12723 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.796276534289 : ℝ) ≤ √(12723 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12723 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12723 Θ 1.22 ≤ 0.011756598186 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.796276534289 := by gcongr <;> linarith
      _ ≤ (0.011756598186 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12723 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12723 12723 0.011 ≤ 0.008474455468 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12723 12723 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12723 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12723 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12723 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12723 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162092930738 + 0.011756598186 + (0.008474455468 : ℝ) *
        (1 + 2 * (0.282131843024 + 0.011756598186) / (0.560504606539 * 112.796276534289))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12723]

end BstLean.Part269.N12723

/-! The original eight local profiles supply actual 12723 moment certificates. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12723 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052760025068 ∧
    0 ≤ bN 12723 BstLean.Part154.csC (groupTheta g) ∧ bN 12723 BstLean.Part154.csC (groupTheta g) ≤ 0.001377797825 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12723 12723 0.011
      (momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12723 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12723 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12723 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229695505111 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12723 0.011
      (momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12723 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12723
/-! The actual computed-centre upper energy formula at 12723. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12723

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12723)
open BstLean.Part268 (cell12723)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085423465929
  | 2 => 0.086364994538
  | 3 => 0.087304485743
  | 4 => 0.088243316748
  | 5 => 0.089183154693
  | 6 => 0.090125999896
  | 7 => 0.091074233182
  | 8 => 0.092030667378
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12723 12723 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12723 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12723

/-! Actual upper energy certificates on all 43 source endpoints at 12723. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12723)
open BstLean.Part268 (cell12723)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12723 (gMinus 12723) (1 - (cell12723 i).lower) ≤ 1 ∧
    energyUpper 12723 (gMinus 12723) (BstLean.Part211.gPlus 12723)
      (finiteEnergy 12723 12723 0.011) (1 - (cell12723 i).lower) ≤
      (cell12723 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨10,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨11,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨12,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨13,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨14,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨15,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨16,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨17,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨18,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨19,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨20,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨21,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨22,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨23,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨24,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨25,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨26,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨27,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨28,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨29,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨30,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨31,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨32,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨33,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨34,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨35,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨36,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨37,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨38,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨39,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨40,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨41,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨42,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨43,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨44,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨45,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨46,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨47,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨48,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨49,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨50,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨51,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12723) (by norm_num)
        (q := 1 - (cell12723 ⟨52,by decide⟩).lower)
        (by norm_num [cell12723]) (by norm_num [cell12723])
      exact ⟨E.1,E.2.trans (by norm_num [cell12723])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12723

/-! Source-cell containment and simple scalar guards at 12723. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12723)
open BstLean.Part268 (cell12723)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12723 ⟨10,by decide⟩).lower ∧ (cell12723 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12723 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12723 ⟨11,by decide⟩).lower ∧ (cell12723 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12723 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12723 ⟨12,by decide⟩).lower ∧ (cell12723 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12723 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12723 ⟨13,by decide⟩).lower ∧ (cell12723 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12723 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12723 ⟨14,by decide⟩).lower ∧ (cell12723 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12723 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12723 ⟨15,by decide⟩).lower ∧ (cell12723 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12723 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12723 ⟨16,by decide⟩).lower ∧ (cell12723 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12723 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12723 ⟨17,by decide⟩).lower ∧ (cell12723 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12723 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12723 ⟨18,by decide⟩).lower ∧ (cell12723 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12723 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12723 ⟨19,by decide⟩).lower ∧ (cell12723 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12723 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12723 ⟨20,by decide⟩).lower ∧ (cell12723 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12723 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12723 ⟨21,by decide⟩).lower ∧ (cell12723 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12723 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12723 ⟨22,by decide⟩).lower ∧ (cell12723 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12723 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12723 ⟨23,by decide⟩).lower ∧ (cell12723 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12723 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12723 ⟨24,by decide⟩).lower ∧ (cell12723 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12723 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12723 ⟨25,by decide⟩).lower ∧ (cell12723 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12723 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12723 ⟨26,by decide⟩).lower ∧ (cell12723 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12723 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12723 ⟨27,by decide⟩).lower ∧ (cell12723 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12723 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12723 ⟨28,by decide⟩).lower ∧ (cell12723 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12723 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12723 ⟨29,by decide⟩).lower ∧ (cell12723 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12723 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12723 ⟨30,by decide⟩).lower ∧ (cell12723 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12723 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12723 ⟨31,by decide⟩).lower ∧ (cell12723 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12723 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12723 ⟨32,by decide⟩).lower ∧ (cell12723 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12723 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12723 ⟨33,by decide⟩).lower ∧ (cell12723 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12723 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12723 ⟨34,by decide⟩).lower ∧ (cell12723 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12723 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12723 ⟨35,by decide⟩).lower ∧ (cell12723 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12723 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12723 ⟨36,by decide⟩).lower ∧ (cell12723 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12723 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12723 ⟨37,by decide⟩).lower ∧ (cell12723 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12723 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12723 ⟨38,by decide⟩).lower ∧ (cell12723 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12723 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12723 ⟨39,by decide⟩).lower ∧ (cell12723 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12723 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12723 ⟨40,by decide⟩).lower ∧ (cell12723 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12723 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12723 ⟨41,by decide⟩).lower ∧ (cell12723 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12723 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12723 ⟨42,by decide⟩).lower ∧ (cell12723 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12723 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12723 ⟨43,by decide⟩).lower ∧ (cell12723 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12723 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12723 ⟨44,by decide⟩).lower ∧ (cell12723 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12723 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12723 ⟨45,by decide⟩).lower ∧ (cell12723 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12723 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12723 ⟨46,by decide⟩).lower ∧ (cell12723 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12723 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12723 ⟨47,by decide⟩).lower ∧ (cell12723 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12723 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12723 ⟨48,by decide⟩).lower ∧ (cell12723 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12723 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12723 ⟨49,by decide⟩).lower ∧ (cell12723 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12723 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12723 ⟨50,by decide⟩).lower ∧ (cell12723 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12723 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12723 ⟨51,by decide⟩).lower ∧ (cell12723 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12723 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12723 ⟨52,by decide⟩).lower ∧ (cell12723 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12723 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12723 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12723 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12723,cell12723,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12723 i).lower ∧
    (cell12723 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12723 i).upper ≤ (0.532 : ℝ) ∧
    (cell12723 i).centre ≤ (0.1 : ℝ) ∧ (cell12723 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12723 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12723 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12723

/-! The local source numeric instances at 12723 have no network premises. -/
namespace BstLean.Part269.N12723
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12723)
open BstLean.Part268 (cell12723)

noncomputable def sourceNumerics12723 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12723 (cell12723 i)
      scalarRow12723.M scalarRow12723.H scalarRow12723.xi := by
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
    energy_allowance := scalarRow12723.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12723]
    centre_nonneg := (scalarRow12723.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12723])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12723
/-! Actual 12724 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12724 ≤ (1.035775136504 : ℝ) := by
  have hr : (112.800709217628 : ℝ) ≤ √(12724 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.800709217628 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12724 12724 (11 / 1000) ≤
    (0.008474122449 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12724) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.800709217628 : ℝ) ≤ √(12724 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12724)
  have hdiv : K / √(12724 : ℝ) ≤ K / 112.800709217628 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.800709217628 ≤ (0.008474122449 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12724.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12724 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12724 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12724 := gPlus_lower 12724
end BstLean.Part269.N12724

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12724
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035775136503 : ℝ) ≤ wn 12724 := by
  have hn : √(12724 : ℝ) ≤ 112.800709217629 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12724 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.800709217629 ≤ 2 / √(12724 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251397499 : ℝ) ≤ rhoBar 12724 BstLean.Part154.csC ∧
    rhoBar 12724 BstLean.Part154.csC ≤ 0.000251397888 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035775136503 : ℝ) / (1.295212 * 12724) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035775136504 : ℝ) / (1.29521 * 12724) := by gcongr
      _ ≤ (0.000251397888 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12724 BstLean.Part154.csC) ≤ 0.001005654753 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12724 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) ≤ 0.000192019386 ∧
    cc1 (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) ≤ 0.000122183214 ∧
    cc2 (rhoBar 12724 BstLean.Part154.csC) ≤ 0.000070928296 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12724 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12724 BstLean.Part154.csC * nuR (rhoBar 12724 BstLean.Part154.csC)) ≤ 0.000502811577 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251397888 : ℝ) * 0.001005654753 := by gcongr
      _ ≤ (0.000502811577 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12724 BstLean.Part154.csC) * nuR (rhoBar 12724 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001005654753 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12724 BstLean.Part154.csC) * rhoBar 12724 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251397888 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251397888 / 2 + 0.399 * 0.001005654753 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192019386 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502811577 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122183214 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251397888 / 1.414213562 := by gcongr
      _ ≤ (0.000070928296 : ℝ) := by norm_num

end BstLean.Part269.N12724

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12724
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) ≤ 1.59230E-7 := by
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12724 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12724 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192019386 : ℝ) ^ 2 + 0.000122183214 ^ 2 + 3 * 0.000070928296 ^ 2 +
        2 * 0.797885 * 0.000192019386 * 0.000122183214 + 2 * 0.000192019386 * 0.000070928296 +
        4 * 0.797885 * 0.000122183214 * 0.000070928296 := by gcongr
    _ ≤ (1.59230E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12724 BstLean.Part154.csC Θ ≤ 0.002624154587 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12724 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12724 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035775136504 * 1.59230E-7 / (0.000251397499 : ℝ) := by gcongr
    _ ≤ 0.002624154587 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12724 BstLean.Part154.csC Θ ≤ 0.002911547538 + 0.000663082111 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12724 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035775136504 : ℝ) * ((2 * Θ * 0.000251397888 +
        (6863 / 10000) * 0.000251397888 * 12724 * 0.001005654753) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002911547538 + 0.000663082111 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12724 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12724 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12724 0.011 Θ ∧ gammaRatio 12724 0.011 Θ ≤ 0.000086424093 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12724 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035775136504 : ℝ) * 0.525 / ((1 - 0.011) * 12724) := by gcongr
      _ ≤ (0.000086424093 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12724 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12724 0.011 Θ) :=
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
    badAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12724 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12724 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12724 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12724 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12724 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12724 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12724 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12724 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12724 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12724 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035775136504 : ℝ) * 12724 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003527240015 + 0.003287236698 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12724

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12724
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12724 BstLean.Part154.csC) (piBar (rhoBar 12724 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12724 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12724 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12724 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12724 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12724 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12724 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12724 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12724 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12724 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052434255021 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12724) ≤ 0.010587146033 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12724 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035775136504)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010587146033 + 2 * 0.737676 / 12724) := by gcongr
    _ ≤ (0.052434255021 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12724 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12724

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12724
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504651595 : ℝ) ≤ plow 12724 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12724) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052759639282)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377681159) : eMP 12724 0.011 xi bn ≤ 0.001186093956 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12724 : ℝ) * (1 - 0.011))) ≤ 0.000586461280 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001377681159 / (12724 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000586461280 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000586461280 : ℝ) + 3.141593 * 0.052759639282 / (12724 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001186093956 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052759639282)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377681159) : PiBarMP 12724 12 0.011 xi bn ≤ 0.161097509999 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12724 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037117127570 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.178589757582 : ℝ) ≤ √((12724 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.800709217628 : ℝ) ≤ √(12724 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12724) ≤ 0.123513481072 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037117127570 + 0.052759639282 * 1.772454 / (2 * (112.178589757582 : ℝ))) * (1 + 0.001186093956) +
        8 / (12724 * 112.800709217628) + 0.123513481072 := by gcongr
    _ ≤ (0.161097509999 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052759639282)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377681159) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282128920354) :
    parallelOracle 12724 0.011 xi bn cd ≤ 0.162086409620 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12724 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12724 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504651595 : ℝ) ≤ plow 12724 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.800709217628 : ℝ) ≤ √(12724 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282128920354 : ℝ) / (2 * 0.560504651595 * 112.800709217628)) * 0.161097509999 +
        0.282128920354 ^ 2 / (2 * 0.560504651595 * 112.800709217628) := by gcongr
    _ ≤ (0.162086409620 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052759639282) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001377681159)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282128920354) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12724 12724 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504651595 : ℝ) ≤ plow 12724 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.800709217628 : ℝ) ≤ √(12724 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12724 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12724 Θ 1.22 ≤ 0.011756136191 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.800709217628 := by gcongr <;> linarith
      _ ≤ (0.011756136191 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12724 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12724 12724 0.011 ≤ 0.008474122449 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12724 12724 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12724 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12724 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12724 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12724 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162086409620 + 0.011756136191 + (0.008474122449 : ℝ) *
        (1 + 2 * (0.282128920354 + 0.011756136191) / (0.560504651595 * 112.800709217628))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12724]

end BstLean.Part269.N12724

/-! The original eight local profiles supply actual 12724 moment certificates. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12724 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052759639282 ∧
    0 ≤ bN 12724 BstLean.Part154.csC (groupTheta g) ∧ bN 12724 BstLean.Part154.csC (groupTheta g) ≤ 0.001377681159 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12724 12724 0.011
      (momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12724 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12724 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12724 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229694665333 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12724 0.011
      (momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12724 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12724
/-! The actual computed-centre upper energy formula at 12724. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12724

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12724)
open BstLean.Part268 (cell12724)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085420574807
  | 2 => 0.086362050867
  | 3 => 0.087301481949
  | 4 => 0.088240243505
  | 5 => 0.089180000616
  | 6 => 0.090122751185
  | 7 => 0.091070873240
  | 8 => 0.092027176372
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12724 12724 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12724 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12724

/-! Actual upper energy certificates on all 43 source endpoints at 12724. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12724)
open BstLean.Part268 (cell12724)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12724 (gMinus 12724) (1 - (cell12724 i).lower) ≤ 1 ∧
    energyUpper 12724 (gMinus 12724) (BstLean.Part211.gPlus 12724)
      (finiteEnergy 12724 12724 0.011) (1 - (cell12724 i).lower) ≤
      (cell12724 i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨10,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨11,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨12,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨13,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨14,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨15,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨16,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨17,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨18,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨19,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨20,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨21,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨22,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨23,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨24,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨25,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨26,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨27,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨28,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨29,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨30,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨31,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨32,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨33,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨34,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨35,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨36,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨37,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨38,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨39,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨40,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨41,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨42,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨43,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨44,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨45,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨46,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨47,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨48,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨49,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨50,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨51,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12724) (by norm_num)
        (q := 1 - (cell12724 ⟨52,by decide⟩).lower)
        (by norm_num [cell12724]) (by norm_num [cell12724])
      exact ⟨E.1,E.2.trans (by norm_num [cell12724])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12724

/-! Source-cell containment and simple scalar guards at 12724. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12724)
open BstLean.Part268 (cell12724)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12724 ⟨10,by decide⟩).lower ∧ (cell12724 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12724 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12724 ⟨11,by decide⟩).lower ∧ (cell12724 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12724 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12724 ⟨12,by decide⟩).lower ∧ (cell12724 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12724 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12724 ⟨13,by decide⟩).lower ∧ (cell12724 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12724 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12724 ⟨14,by decide⟩).lower ∧ (cell12724 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12724 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12724 ⟨15,by decide⟩).lower ∧ (cell12724 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12724 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12724 ⟨16,by decide⟩).lower ∧ (cell12724 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12724 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12724 ⟨17,by decide⟩).lower ∧ (cell12724 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12724 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12724 ⟨18,by decide⟩).lower ∧ (cell12724 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12724 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12724 ⟨19,by decide⟩).lower ∧ (cell12724 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12724 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12724 ⟨20,by decide⟩).lower ∧ (cell12724 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12724 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12724 ⟨21,by decide⟩).lower ∧ (cell12724 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12724 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12724 ⟨22,by decide⟩).lower ∧ (cell12724 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12724 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12724 ⟨23,by decide⟩).lower ∧ (cell12724 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12724 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12724 ⟨24,by decide⟩).lower ∧ (cell12724 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12724 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12724 ⟨25,by decide⟩).lower ∧ (cell12724 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12724 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12724 ⟨26,by decide⟩).lower ∧ (cell12724 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12724 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12724 ⟨27,by decide⟩).lower ∧ (cell12724 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12724 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12724 ⟨28,by decide⟩).lower ∧ (cell12724 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12724 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12724 ⟨29,by decide⟩).lower ∧ (cell12724 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12724 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12724 ⟨30,by decide⟩).lower ∧ (cell12724 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12724 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12724 ⟨31,by decide⟩).lower ∧ (cell12724 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12724 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12724 ⟨32,by decide⟩).lower ∧ (cell12724 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12724 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12724 ⟨33,by decide⟩).lower ∧ (cell12724 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12724 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12724 ⟨34,by decide⟩).lower ∧ (cell12724 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12724 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12724 ⟨35,by decide⟩).lower ∧ (cell12724 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12724 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12724 ⟨36,by decide⟩).lower ∧ (cell12724 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12724 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12724 ⟨37,by decide⟩).lower ∧ (cell12724 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12724 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12724 ⟨38,by decide⟩).lower ∧ (cell12724 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12724 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12724 ⟨39,by decide⟩).lower ∧ (cell12724 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12724 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12724 ⟨40,by decide⟩).lower ∧ (cell12724 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12724 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12724 ⟨41,by decide⟩).lower ∧ (cell12724 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12724 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12724 ⟨42,by decide⟩).lower ∧ (cell12724 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12724 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12724 ⟨43,by decide⟩).lower ∧ (cell12724 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12724 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12724 ⟨44,by decide⟩).lower ∧ (cell12724 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12724 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12724 ⟨45,by decide⟩).lower ∧ (cell12724 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12724 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12724 ⟨46,by decide⟩).lower ∧ (cell12724 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12724 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12724 ⟨47,by decide⟩).lower ∧ (cell12724 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12724 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12724 ⟨48,by decide⟩).lower ∧ (cell12724 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12724 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12724 ⟨49,by decide⟩).lower ∧ (cell12724 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12724 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12724 ⟨50,by decide⟩).lower ∧ (cell12724 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12724 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12724 ⟨51,by decide⟩).lower ∧ (cell12724 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12724 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12724 ⟨52,by decide⟩).lower ∧ (cell12724 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12724 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12724 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12724 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12724,cell12724,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12724 i).lower ∧
    (cell12724 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12724 i).upper ≤ (0.532 : ℝ) ∧
    (cell12724 i).centre ≤ (0.1 : ℝ) ∧ (cell12724 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12724 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12724 i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
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

end BstLean.Part269.N12724

/-! The local source numeric instances at 12724 have no network premises. -/
namespace BstLean.Part269.N12724
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12724)
open BstLean.Part268 (cell12724)

noncomputable def sourceNumerics12724 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12724 (cell12724 i)
      scalarRow12724.M scalarRow12724.H scalarRow12724.xi := by
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
    energy_allowance := scalarRow12724.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12724]
    centre_nonneg := (scalarRow12724.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12724])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12724