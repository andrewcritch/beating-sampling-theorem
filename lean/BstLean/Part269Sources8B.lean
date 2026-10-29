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
import BstLean.Part269Direction8
import BstLean.Part269Shared8
import BstLean.Part269Finite
import BstLean.Part269Rows8
import BstLean.Part269Source
/-! Actual 12563 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12563 ≤ (1.036005664041 : ℝ) := by
  have hr : (112.084789333789 : ℝ) ≤ √(12563 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.084789333789 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12563 12563 (11 / 1000) ≤
    (0.008528249684 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12563) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.084789333789 : ℝ) ≤ √(12563 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12563)
  have hdiv : K / √(12563 : ℝ) ≤ K / 112.084789333789 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.084789333789 ≤ (0.008528249684 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12563.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12563 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12563 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12563 := gPlus_lower 12563
end BstLean.Part269.N12563

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12563
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036005664040 : ℝ) ≤ wn 12563 := by
  have hn : √(12563 : ℝ) ≤ 112.084789333790 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12563 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.084789333790 ≤ 2 / √(12563 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254675930 : ℝ) ≤ rhoBar 12563 BstLean.Part154.csC ∧
    rhoBar 12563 BstLean.Part154.csC ≤ 0.000254676324 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036005664040 : ℝ) / (1.295212 * 12563) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036005664041 : ℝ) / (1.29521 * 12563) := by gcongr
      _ ≤ (0.000254676324 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12563 BstLean.Part154.csC) ≤ 0.001018770157 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12563 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) ≤ 0.000194523595 ∧
    cc1 (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) ≤ 0.000123776634 ∧
    cc2 (rhoBar 12563 BstLean.Part154.csC) ≤ 0.000071853259 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12563 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12563 BstLean.Part154.csC * nuR (rhoBar 12563 BstLean.Part154.csC)) ≤ 0.000509368863 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254676324 : ℝ) * 0.001018770157 := by gcongr
      _ ≤ (0.000509368863 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12563 BstLean.Part154.csC) * nuR (rhoBar 12563 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018770157 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12563 BstLean.Part154.csC) * rhoBar 12563 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254676324 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254676324 / 2 + 0.399 * 0.001018770157 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194523595 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509368863 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123776634 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254676324 / 1.414213562 := by gcongr
      _ ≤ (0.000071853259 : ℝ) := by norm_num

end BstLean.Part269.N12563

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12563
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) ≤ 1.63410E-7 := by
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12563 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12563 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194523595 : ℝ) ^ 2 + 0.000123776634 ^ 2 + 3 * 0.000071853259 ^ 2 +
        2 * 0.797885 * 0.000194523595 * 0.000123776634 + 2 * 0.000194523595 * 0.000071853259 +
        4 * 0.797885 * 0.000123776634 * 0.000071853259 := by gcongr
    _ ≤ (1.63410E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12563 BstLean.Part154.csC Θ ≤ 0.002658966406 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12563 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12563 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036005664041 * 1.63410E-7 / (0.000254675930 : ℝ) := by gcongr
    _ ≤ 0.002658966406 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12563 BstLean.Part154.csC Θ ≤ 0.002950832002 + 0.000671878753 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12563 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036005664041 : ℝ) * ((2 * Θ * 0.000254676324 +
        (6863 / 10000) * 0.000254676324 * 12563 * 0.001018770157) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002950832002 + 0.000671878753 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12563 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12563 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12563 0.011 Θ ∧ gammaRatio 12563 0.011 Θ ≤ 0.000087551135 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12563 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036005664041 : ℝ) * 0.525 / ((1 - 0.011) * 12563) := by gcongr
      _ ≤ (0.000087551135 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12563 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12563 0.011 Θ) :=
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
    badAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12563 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12563 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12563 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12563 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12563 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12563 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12563 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12563 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12563 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12563 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036005664041 : ℝ) * 12563 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003694572742 + 0.003330845159 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12563

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12563
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12563 BstLean.Part154.csC) (piBar (rhoBar 12563 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12563 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12563 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12563 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12563 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12563 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12563 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12563 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12563 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12563 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052772820081 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12563) ≤ 0.010654769378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12563 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036005664041)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010654769378 + 2 * 0.737676 / 12563) := by gcongr
    _ ≤ (0.052772820081 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12563 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12563

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12563
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497305181 : ℝ) ≤ plow 12563 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12563) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949866451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395957364) : eMP 12563 0.011 xi bn ≤ 0.001201606511 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12563 : ℝ) * (1 - 0.011))) ≤ 0.000594109110 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395957364 / (12563 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594109110 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594109110 : ℝ) + 3.141593 * 0.052949866451 / (12563 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201606511 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949866451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395957364) : PiBarMP 12563 12 0.011 xi bn ≤ 0.162136978000 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12563 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037362512817 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.466618321361 : ℝ) ≤ √((12563 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.084789333789 : ℝ) ≤ √(12563 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12563) ≤ 0.124302399510 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037362512817 + 0.052949866451 * 1.772454 / (2 * (111.466618321361 : ℝ))) * (1 + 0.001201606511) +
        8 / (12563 * 112.084789333789) + 0.124302399510 := by gcongr
    _ ≤ (0.162136978000 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949866451)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395957364) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282881199875) :
    parallelOracle 12563 0.011 xi bn cd ≤ 0.163138894739 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12563 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12563 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497305181 : ℝ) ≤ plow 12563 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.084789333789 : ℝ) ≤ √(12563 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282881199875 : ℝ) / (2 * 0.560497305181 * 112.084789333789)) * 0.162136978000 +
        0.282881199875 ^ 2 / (2 * 0.560497305181 * 112.084789333789) := by gcongr
    _ ≤ (0.163138894739 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949866451) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395957364)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282881199875) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12563 12563 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497305181 : ℝ) ≤ plow 12563 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.084789333789 : ℝ) ≤ √(12563 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12563 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12563 Θ 1.22 ≤ 0.011831226235 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.084789333789 := by gcongr <;> linarith
      _ ≤ (0.011831226235 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12563 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12563 12563 0.011 ≤ 0.008528249684 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12563 12563 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12563 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12563 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12563 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12563 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163138894739 + 0.011831226235 + (0.008528249684 : ℝ) *
        (1 + 2 * (0.282881199875 + 0.011831226235) / (0.560497305181 * 112.084789333789))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12563]

end BstLean.Part269.N12563

/-! The original eight local profiles supply actual 12563 moment certificates. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12563 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052949866451 ∧
    0 ≤ bN 12563 BstLean.Part154.csC (groupTheta g) ∧ bN 12563 BstLean.Part154.csC (groupTheta g) ≤ 0.001395957364 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12563 12563 0.011
      (momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12563 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12563 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12563 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230108379794 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12563 0.011
      (momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12563 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12563
/-! The actual computed-centre upper energy formula at 12563. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12563

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12563)
open BstLean.Part268 (cell12563)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085900452935
  | 2 => 0.086850985904
  | 3 => 0.087800833444
  | 4 => 0.088751681338
  | 5 => 0.089705559275
  | 6 => 0.090664890711
  | 7 => 0.091632547174
  | 8 => 0.092611907058
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12563 12563 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12563 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12563

/-! Actual upper energy certificates on all 43 source endpoints at 12563. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12563)
open BstLean.Part268 (cell12563)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12563 (gMinus 12563) (1 - (cell12563 i).lower) ≤ 1 ∧
    energyUpper 12563 (gMinus 12563) (BstLean.Part211.gPlus 12563)
      (finiteEnergy 12563 12563 0.011) (1 - (cell12563 i).lower) ≤
      (cell12563 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨10,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨11,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨12,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨13,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨14,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨15,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨16,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨17,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨18,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨19,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨20,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨21,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨22,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨23,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨24,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨25,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨26,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨27,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨28,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨29,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨30,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨31,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨32,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨33,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨34,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨35,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨36,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨37,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨38,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨39,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨40,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨41,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨42,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨43,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨44,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨45,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨46,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨47,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨48,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨49,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨50,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨51,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12563) (by norm_num)
        (q := 1 - (cell12563 ⟨52,by decide⟩).lower)
        (by norm_num [cell12563]) (by norm_num [cell12563])
      exact ⟨E.1,E.2.trans (by norm_num [cell12563])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12563

/-! Source-cell containment and simple scalar guards at 12563. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12563)
open BstLean.Part268 (cell12563)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12563 ⟨10,by decide⟩).lower ∧ (cell12563 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12563 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12563 ⟨11,by decide⟩).lower ∧ (cell12563 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12563 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12563 ⟨12,by decide⟩).lower ∧ (cell12563 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12563 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12563 ⟨13,by decide⟩).lower ∧ (cell12563 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12563 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12563 ⟨14,by decide⟩).lower ∧ (cell12563 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12563 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12563 ⟨15,by decide⟩).lower ∧ (cell12563 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12563 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12563 ⟨16,by decide⟩).lower ∧ (cell12563 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12563 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12563 ⟨17,by decide⟩).lower ∧ (cell12563 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12563 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12563 ⟨18,by decide⟩).lower ∧ (cell12563 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12563 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12563 ⟨19,by decide⟩).lower ∧ (cell12563 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12563 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12563 ⟨20,by decide⟩).lower ∧ (cell12563 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12563 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12563 ⟨21,by decide⟩).lower ∧ (cell12563 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12563 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12563 ⟨22,by decide⟩).lower ∧ (cell12563 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12563 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12563 ⟨23,by decide⟩).lower ∧ (cell12563 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12563 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12563 ⟨24,by decide⟩).lower ∧ (cell12563 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12563 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12563 ⟨25,by decide⟩).lower ∧ (cell12563 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12563 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12563 ⟨26,by decide⟩).lower ∧ (cell12563 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12563 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12563 ⟨27,by decide⟩).lower ∧ (cell12563 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12563 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12563 ⟨28,by decide⟩).lower ∧ (cell12563 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12563 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12563 ⟨29,by decide⟩).lower ∧ (cell12563 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12563 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12563 ⟨30,by decide⟩).lower ∧ (cell12563 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12563 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12563 ⟨31,by decide⟩).lower ∧ (cell12563 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12563 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12563 ⟨32,by decide⟩).lower ∧ (cell12563 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12563 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12563 ⟨33,by decide⟩).lower ∧ (cell12563 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12563 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12563 ⟨34,by decide⟩).lower ∧ (cell12563 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12563 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12563 ⟨35,by decide⟩).lower ∧ (cell12563 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12563 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12563 ⟨36,by decide⟩).lower ∧ (cell12563 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12563 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12563 ⟨37,by decide⟩).lower ∧ (cell12563 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12563 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12563 ⟨38,by decide⟩).lower ∧ (cell12563 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12563 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12563 ⟨39,by decide⟩).lower ∧ (cell12563 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12563 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12563 ⟨40,by decide⟩).lower ∧ (cell12563 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12563 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12563 ⟨41,by decide⟩).lower ∧ (cell12563 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12563 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12563 ⟨42,by decide⟩).lower ∧ (cell12563 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12563 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12563 ⟨43,by decide⟩).lower ∧ (cell12563 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12563 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12563 ⟨44,by decide⟩).lower ∧ (cell12563 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12563 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12563 ⟨45,by decide⟩).lower ∧ (cell12563 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12563 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12563 ⟨46,by decide⟩).lower ∧ (cell12563 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12563 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12563 ⟨47,by decide⟩).lower ∧ (cell12563 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12563 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12563 ⟨48,by decide⟩).lower ∧ (cell12563 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12563 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12563 ⟨49,by decide⟩).lower ∧ (cell12563 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12563 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12563 ⟨50,by decide⟩).lower ∧ (cell12563 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12563 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12563 ⟨51,by decide⟩).lower ∧ (cell12563 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12563 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12563 ⟨52,by decide⟩).lower ∧ (cell12563 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12563 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12563 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12563 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12563,cell12563,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12563 i).lower ∧
    (cell12563 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12563 i).upper ≤ (0.532 : ℝ) ∧
    (cell12563 i).centre ≤ (0.1 : ℝ) ∧ (cell12563 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12563 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12563 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12563

/-! The local source numeric instances at 12563 have no network premises. -/
namespace BstLean.Part269.N12563
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12563)
open BstLean.Part268 (cell12563)

noncomputable def sourceNumerics12563 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12563 (cell12563 i)
      scalarRow12563.M scalarRow12563.H scalarRow12563.xi := by
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
    energy_allowance := scalarRow12563.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12563]
    centre_nonneg := (scalarRow12563.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12563])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12563
/-! Actual 12564 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12564 ≤ (1.036004218451 : ℝ) := by
  have hr : (112.089250153616 : ℝ) ≤ √(12564 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.089250153616 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12564 12564 (11 / 1000) ≤
    (0.008527910282 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12564) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.089250153616 : ℝ) ≤ √(12564 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12564)
  have hdiv : K / √(12564 : ℝ) ≤ K / 112.089250153616 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.089250153616 ≤ (0.008527910282 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12564.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12564 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12564 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12564 := gPlus_lower 12564
end BstLean.Part269.N12564

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12564
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036004218450 : ℝ) ≤ wn 12564 := by
  have hn : √(12564 : ℝ) ≤ 112.089250153617 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12564 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.089250153617 ≤ 2 / √(12564 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254655305 : ℝ) ≤ rhoBar 12564 BstLean.Part154.csC ∧
    rhoBar 12564 BstLean.Part154.csC ≤ 0.000254655699 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036004218450 : ℝ) / (1.295212 * 12564) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036004218451 : ℝ) / (1.29521 * 12564) := by gcongr
      _ ≤ (0.000254655699 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12564 BstLean.Part154.csC) ≤ 0.001018687646 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12564 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) ≤ 0.000194507840 ∧
    cc1 (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) ≤ 0.000123766610 ∧
    cc2 (rhoBar 12564 BstLean.Part154.csC) ≤ 0.000071847440 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12564 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12564 BstLean.Part154.csC * nuR (rhoBar 12564 BstLean.Part154.csC)) ≤ 0.000509327611 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254655699 : ℝ) * 0.001018687646 := by gcongr
      _ ≤ (0.000509327611 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12564 BstLean.Part154.csC) * nuR (rhoBar 12564 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018687646 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12564 BstLean.Part154.csC) * rhoBar 12564 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254655699 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254655699 / 2 + 0.399 * 0.001018687646 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194507840 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509327611 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123766610 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254655699 / 1.414213562 := by gcongr
      _ ≤ (0.000071847440 : ℝ) := by norm_num

end BstLean.Part269.N12564

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12564
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) ≤ 1.63384E-7 := by
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12564 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12564 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194507840 : ℝ) ^ 2 + 0.000123766610 ^ 2 + 3 * 0.000071847440 ^ 2 +
        2 * 0.797885 * 0.000194507840 * 0.000123766610 + 2 * 0.000194507840 * 0.000071847440 +
        4 * 0.797885 * 0.000123766610 * 0.000071847440 := by gcongr
    _ ≤ (1.63384E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12564 BstLean.Part154.csC Θ ≤ 0.002658754951 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12564 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12564 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036004218451 * 1.63384E-7 / (0.000254655305 : ℝ) := by gcongr
    _ ≤ 0.002658754951 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12564 BstLean.Part154.csC Θ ≤ 0.002950584785 + 0.000671823403 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12564 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036004218451 : ℝ) * ((2 * Θ * 0.000254655699 +
        (6863 / 10000) * 0.000254655699 * 12564 * 0.001018687646) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002950584785 + 0.000671823403 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12564 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12564 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12564 0.011 Θ ∧ gammaRatio 12564 0.011 Θ ≤ 0.000087544044 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12564 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036004218451 : ℝ) * 0.525 / ((1 - 0.011) * 12564) := by gcongr
      _ ≤ (0.000087544044 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12564 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12564 0.011 Θ) :=
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
    badAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12564 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12564 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12564 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12564 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12564 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12564 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12564 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12564 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12564 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12564 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036004218451 : ℝ) * 12564 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003694325525 + 0.003330578354 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12564

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12564
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12564 BstLean.Part154.csC) (piBar (rhoBar 12564 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12564 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12564 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12564 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12564 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12564 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12564 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12564 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12564 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12564 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052770696985 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12564) ≤ 0.010654345350 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12564 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036004218451)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010654345350 + 2 * 0.737676 / 12564) := by gcongr
    _ ≤ (0.052770696985 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12564 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12564

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12564
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497351392 : ℝ) ≤ plow 12564 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12564) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949479161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395846350) : eMP 12564 0.011 xi bn ≤ 0.001201510816 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12564 : ℝ) * (1 - 0.011))) ≤ 0.000594061844 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395846350 / (12564 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594061844 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594061844 : ℝ) + 3.141593 * 0.052949479161 / (12564 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201510816 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949479161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395846350) : PiBarMP 12564 12 0.011 xi bn ≤ 0.162130519534 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12564 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037361027154 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.471054538835 : ℝ) ≤ √((12564 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.089250153616 : ℝ) ≤ √(12564 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12564) ≤ 0.124297452643 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037361027154 + 0.052949479161 * 1.772454 / (2 * (111.471054538835 : ℝ))) * (1 + 0.001201510816) +
        8 / (12564 * 112.089250153616) + 0.124297452643 := by gcongr
    _ ≤ (0.162130519534 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949479161)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395846350) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282878235239) :
    parallelOracle 12564 0.011 xi bn cd ≤ 0.163132364603 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12564 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12564 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497351392 : ℝ) ≤ plow 12564 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.089250153616 : ℝ) ≤ √(12564 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282878235239 : ℝ) / (2 * 0.560497351392 * 112.089250153616)) * 0.162130519534 +
        0.282878235239 ^ 2 / (2 * 0.560497351392 * 112.089250153616) := by gcongr
    _ ≤ (0.163132364603 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949479161) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395846350)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282878235239) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12564 12564 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497351392 : ℝ) ≤ plow 12564 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.089250153616 : ℝ) ≤ √(12564 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12564 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12564 Θ 1.22 ≤ 0.011830755387 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.089250153616 := by gcongr <;> linarith
      _ ≤ (0.011830755387 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12564 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12564 12564 0.011 ≤ 0.008527910282 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12564 12564 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12564 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12564 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12564 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12564 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163132364603 + 0.011830755387 + (0.008527910282 : ℝ) *
        (1 + 2 * (0.282878235239 + 0.011830755387) / (0.560497351392 * 112.089250153616))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12564]

end BstLean.Part269.N12564

/-! The original eight local profiles supply actual 12564 moment certificates. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12564 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052949479161 ∧
    0 ≤ bN 12564 BstLean.Part154.csC (groupTheta g) ∧ bN 12564 BstLean.Part154.csC (groupTheta g) ≤ 0.001395846350 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12564 12564 0.011
      (momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12564 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12564 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12564 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230107538254 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12564 0.011
      (momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12564 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12564
/-! The actual computed-centre upper energy formula at 12564. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12564

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12564)
open BstLean.Part268 (cell12564)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085897377825
  | 2 => 0.086847850570
  | 3 => 0.087797628510
  | 4 => 0.088748395314
  | 5 => 0.089702178191
  | 6 => 0.090661397705
  | 7 => 0.091628922042
  | 8 => 0.092608125746
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12564 12564 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12564 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12564

/-! Actual upper energy certificates on all 43 source endpoints at 12564. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12564)
open BstLean.Part268 (cell12564)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12564 (gMinus 12564) (1 - (cell12564 i).lower) ≤ 1 ∧
    energyUpper 12564 (gMinus 12564) (BstLean.Part211.gPlus 12564)
      (finiteEnergy 12564 12564 0.011) (1 - (cell12564 i).lower) ≤
      (cell12564 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨10,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨11,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨12,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨13,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨14,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨15,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨16,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨17,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨18,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨19,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨20,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨21,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨22,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨23,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨24,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨25,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨26,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨27,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨28,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨29,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨30,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨31,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨32,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨33,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨34,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨35,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨36,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨37,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨38,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨39,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨40,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨41,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨42,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨43,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨44,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨45,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨46,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨47,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨48,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨49,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨50,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨51,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12564) (by norm_num)
        (q := 1 - (cell12564 ⟨52,by decide⟩).lower)
        (by norm_num [cell12564]) (by norm_num [cell12564])
      exact ⟨E.1,E.2.trans (by norm_num [cell12564])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12564

/-! Source-cell containment and simple scalar guards at 12564. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12564)
open BstLean.Part268 (cell12564)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12564 ⟨10,by decide⟩).lower ∧ (cell12564 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12564 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12564 ⟨11,by decide⟩).lower ∧ (cell12564 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12564 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12564 ⟨12,by decide⟩).lower ∧ (cell12564 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12564 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12564 ⟨13,by decide⟩).lower ∧ (cell12564 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12564 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12564 ⟨14,by decide⟩).lower ∧ (cell12564 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12564 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12564 ⟨15,by decide⟩).lower ∧ (cell12564 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12564 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12564 ⟨16,by decide⟩).lower ∧ (cell12564 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12564 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12564 ⟨17,by decide⟩).lower ∧ (cell12564 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12564 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12564 ⟨18,by decide⟩).lower ∧ (cell12564 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12564 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12564 ⟨19,by decide⟩).lower ∧ (cell12564 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12564 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12564 ⟨20,by decide⟩).lower ∧ (cell12564 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12564 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12564 ⟨21,by decide⟩).lower ∧ (cell12564 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12564 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12564 ⟨22,by decide⟩).lower ∧ (cell12564 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12564 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12564 ⟨23,by decide⟩).lower ∧ (cell12564 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12564 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12564 ⟨24,by decide⟩).lower ∧ (cell12564 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12564 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12564 ⟨25,by decide⟩).lower ∧ (cell12564 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12564 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12564 ⟨26,by decide⟩).lower ∧ (cell12564 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12564 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12564 ⟨27,by decide⟩).lower ∧ (cell12564 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12564 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12564 ⟨28,by decide⟩).lower ∧ (cell12564 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12564 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12564 ⟨29,by decide⟩).lower ∧ (cell12564 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12564 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12564 ⟨30,by decide⟩).lower ∧ (cell12564 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12564 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12564 ⟨31,by decide⟩).lower ∧ (cell12564 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12564 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12564 ⟨32,by decide⟩).lower ∧ (cell12564 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12564 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12564 ⟨33,by decide⟩).lower ∧ (cell12564 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12564 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12564 ⟨34,by decide⟩).lower ∧ (cell12564 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12564 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12564 ⟨35,by decide⟩).lower ∧ (cell12564 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12564 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12564 ⟨36,by decide⟩).lower ∧ (cell12564 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12564 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12564 ⟨37,by decide⟩).lower ∧ (cell12564 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12564 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12564 ⟨38,by decide⟩).lower ∧ (cell12564 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12564 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12564 ⟨39,by decide⟩).lower ∧ (cell12564 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12564 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12564 ⟨40,by decide⟩).lower ∧ (cell12564 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12564 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12564 ⟨41,by decide⟩).lower ∧ (cell12564 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12564 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12564 ⟨42,by decide⟩).lower ∧ (cell12564 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12564 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12564 ⟨43,by decide⟩).lower ∧ (cell12564 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12564 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12564 ⟨44,by decide⟩).lower ∧ (cell12564 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12564 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12564 ⟨45,by decide⟩).lower ∧ (cell12564 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12564 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12564 ⟨46,by decide⟩).lower ∧ (cell12564 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12564 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12564 ⟨47,by decide⟩).lower ∧ (cell12564 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12564 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12564 ⟨48,by decide⟩).lower ∧ (cell12564 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12564 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12564 ⟨49,by decide⟩).lower ∧ (cell12564 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12564 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12564 ⟨50,by decide⟩).lower ∧ (cell12564 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12564 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12564 ⟨51,by decide⟩).lower ∧ (cell12564 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12564 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12564 ⟨52,by decide⟩).lower ∧ (cell12564 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12564 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12564 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12564 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12564,cell12564,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12564 i).lower ∧
    (cell12564 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12564 i).upper ≤ (0.532 : ℝ) ∧
    (cell12564 i).centre ≤ (0.1 : ℝ) ∧ (cell12564 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12564 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12564 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12564

/-! The local source numeric instances at 12564 have no network premises. -/
namespace BstLean.Part269.N12564
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12564)
open BstLean.Part268 (cell12564)

noncomputable def sourceNumerics12564 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12564 (cell12564 i)
      scalarRow12564.M scalarRow12564.H scalarRow12564.xi := by
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
    energy_allowance := scalarRow12564.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12564]
    centre_nonneg := (scalarRow12564.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12564])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12564
/-! Actual 12565 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12565 ≤ (1.036002773035 : ℝ) := by
  have hr : (112.093710795922 : ℝ) ≤ √(12565 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.093710795922 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12565 12565 (11 / 1000) ≤
    (0.008527570921 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12565) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.093710795922 : ℝ) ≤ √(12565 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12565)
  have hdiv : K / √(12565 : ℝ) ≤ K / 112.093710795922 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.093710795922 ≤ (0.008527570921 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12565.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12565 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12565 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12565 := gPlus_lower 12565
end BstLean.Part269.N12565

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12565
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036002773034 : ℝ) ≤ wn 12565 := by
  have hn : √(12565 : ℝ) ≤ 112.093710795923 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12565 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.093710795923 ≤ 2 / √(12565 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254634682 : ℝ) ≤ rhoBar 12565 BstLean.Part154.csC ∧
    rhoBar 12565 BstLean.Part154.csC ≤ 0.000254635076 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036002773034 : ℝ) / (1.295212 * 12565) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036002773035 : ℝ) / (1.29521 * 12565) := by gcongr
      _ ≤ (0.000254635076 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12565 BstLean.Part154.csC) ≤ 0.001018605144 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12565 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) ≤ 0.000194492088 ∧
    cc1 (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) ≤ 0.000123756586 ∧
    cc2 (rhoBar 12565 BstLean.Part154.csC) ≤ 0.000071841622 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12565 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12565 BstLean.Part154.csC * nuR (rhoBar 12565 BstLean.Part154.csC)) ≤ 0.000509286362 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254635076 : ℝ) * 0.001018605144 := by gcongr
      _ ≤ (0.000509286362 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12565 BstLean.Part154.csC) * nuR (rhoBar 12565 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018605144 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12565 BstLean.Part154.csC) * rhoBar 12565 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254635076 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254635076 / 2 + 0.399 * 0.001018605144 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194492088 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509286362 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123756586 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254635076 / 1.414213562 := by gcongr
      _ ≤ (0.000071841622 : ℝ) := by norm_num

end BstLean.Part269.N12565

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12565
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) ≤ 1.63358E-7 := by
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12565 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12565 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194492088 : ℝ) ^ 2 + 0.000123756586 ^ 2 + 3 * 0.000071841622 ^ 2 +
        2 * 0.797885 * 0.000194492088 * 0.000123756586 + 2 * 0.000194492088 * 0.000071841622 +
        4 * 0.797885 * 0.000123756586 * 0.000071841622 := by gcongr
    _ ≤ (1.63358E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12565 BstLean.Part154.csC Θ ≤ 0.002658543443 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12565 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12565 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036002773035 * 1.63358E-7 / (0.000254634682 : ℝ) := by gcongr
    _ ≤ 0.002658543443 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12565 BstLean.Part154.csC Θ ≤ 0.002950337581 + 0.000671768059 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12565 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036002773035 : ℝ) * ((2 * Θ * 0.000254635076 +
        (6863 / 10000) * 0.000254635076 * 12565 * 0.001018605144) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002950337581 + 0.000671768059 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12565 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12565 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12565 0.011 Θ ∧ gammaRatio 12565 0.011 Θ ≤ 0.000087536955 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12565 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036002773035 : ℝ) * 0.525 / ((1 - 0.011) * 12565) := by gcongr
      _ ≤ (0.000087536955 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12565 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12565 0.011 Θ) :=
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
    badAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12565 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12565 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12565 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12565 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12565 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12565 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12565 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12565 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12565 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12565 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036002773035 : ℝ) * 12565 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003694078321 + 0.003330311502 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12565

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12565
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12565 BstLean.Part154.csC) (piBar (rhoBar 12565 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12565 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12565 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12565 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12565 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12565 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12565 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12565 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12565 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12565 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052768574141 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12565) ≤ 0.010653921372 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12565 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036002773035)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010653921372 + 2 * 0.737676 / 12565) := by gcongr
    _ ≤ (0.052768574141 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12565 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12565

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12565
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497397596 : ℝ) ≤ plow 12565 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12565) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949091860)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395735308) : eMP 12565 0.011 xi bn ≤ 0.001201415114 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12565 : ℝ) * (1 - 0.011))) ≤ 0.000594014575 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395735308 / (12565 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594014575 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594014575 : ℝ) + 3.141593 * 0.052949091860 / (12565 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201415114 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949091860)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395735308) : PiBarMP 12565 12 0.011 xi bn ≤ 0.162124061228 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12565 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037359541058 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.475490579768 : ℝ) ≤ √((12565 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.093710795922 : ℝ) ≤ √(12565 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12565) ≤ 0.124292506367 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037359541058 + 0.052949091860 * 1.772454 / (2 * (111.475490579768 : ℝ))) * (1 + 0.001201415114) +
        8 / (12565 * 112.093710795922) + 0.124292506367 := by gcongr
    _ ≤ (0.162124061228 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949091860)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395735308) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282875270828) :
    parallelOracle 12565 0.011 xi bn cd ≤ 0.163125834637 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12565 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12565 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497397596 : ℝ) ≤ plow 12565 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.093710795922 : ℝ) ≤ √(12565 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282875270828 : ℝ) / (2 * 0.560497397596 * 112.093710795922)) * 0.162124061228 +
        0.282875270828 ^ 2 / (2 * 0.560497397596 * 112.093710795922) := by gcongr
    _ ≤ (0.163125834637 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052949091860) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395735308)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282875270828) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12565 12565 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497397596 : ℝ) ≤ plow 12565 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.093710795922 : ℝ) ≤ √(12565 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12565 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12565 Θ 1.22 ≤ 0.011830284595 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.093710795922 := by gcongr <;> linarith
      _ ≤ (0.011830284595 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12565 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12565 12565 0.011 ≤ 0.008527570921 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12565 12565 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12565 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12565 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12565 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12565 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163125834637 + 0.011830284595 + (0.008527570921 : ℝ) *
        (1 + 2 * (0.282875270828 + 0.011830284595) / (0.560497397596 * 112.093710795922))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12565]

end BstLean.Part269.N12565

/-! The original eight local profiles supply actual 12565 moment certificates. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12565 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052949091860 ∧
    0 ≤ bN 12565 BstLean.Part154.csC (groupTheta g) ∧ bN 12565 BstLean.Part154.csC (groupTheta g) ≤ 0.001395735308 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12565 12565 0.011
      (momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12565 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12565 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12565 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230106696687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12565 0.011
      (momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12565 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12565
/-! The actual computed-centre upper energy formula at 12565. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12565

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12565)
open BstLean.Part268 (cell12565)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085894303962
  | 2 => 0.086844716536
  | 3 => 0.087794424943
  | 4 => 0.088745110737
  | 5 => 0.089698798651
  | 6 => 0.090657906364
  | 7 => 0.091625298719
  | 8 => 0.092604346416
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12565 12565 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12565 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12565

/-! Actual upper energy certificates on all 43 source endpoints at 12565. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12565)
open BstLean.Part268 (cell12565)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12565 (gMinus 12565) (1 - (cell12565 i).lower) ≤ 1 ∧
    energyUpper 12565 (gMinus 12565) (BstLean.Part211.gPlus 12565)
      (finiteEnergy 12565 12565 0.011) (1 - (cell12565 i).lower) ≤
      (cell12565 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨10,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨11,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨12,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨13,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨14,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨15,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨16,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨17,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨18,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨19,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨20,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨21,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨22,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨23,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨24,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨25,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨26,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨27,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨28,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨29,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨30,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨31,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨32,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨33,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨34,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨35,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨36,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨37,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨38,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨39,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨40,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨41,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨42,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨43,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨44,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨45,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨46,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨47,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨48,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨49,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨50,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨51,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12565) (by norm_num)
        (q := 1 - (cell12565 ⟨52,by decide⟩).lower)
        (by norm_num [cell12565]) (by norm_num [cell12565])
      exact ⟨E.1,E.2.trans (by norm_num [cell12565])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12565

/-! Source-cell containment and simple scalar guards at 12565. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12565)
open BstLean.Part268 (cell12565)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12565 ⟨10,by decide⟩).lower ∧ (cell12565 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12565 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12565 ⟨11,by decide⟩).lower ∧ (cell12565 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12565 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12565 ⟨12,by decide⟩).lower ∧ (cell12565 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12565 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12565 ⟨13,by decide⟩).lower ∧ (cell12565 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12565 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12565 ⟨14,by decide⟩).lower ∧ (cell12565 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12565 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12565 ⟨15,by decide⟩).lower ∧ (cell12565 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12565 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12565 ⟨16,by decide⟩).lower ∧ (cell12565 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12565 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12565 ⟨17,by decide⟩).lower ∧ (cell12565 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12565 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12565 ⟨18,by decide⟩).lower ∧ (cell12565 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12565 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12565 ⟨19,by decide⟩).lower ∧ (cell12565 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12565 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12565 ⟨20,by decide⟩).lower ∧ (cell12565 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12565 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12565 ⟨21,by decide⟩).lower ∧ (cell12565 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12565 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12565 ⟨22,by decide⟩).lower ∧ (cell12565 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12565 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12565 ⟨23,by decide⟩).lower ∧ (cell12565 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12565 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12565 ⟨24,by decide⟩).lower ∧ (cell12565 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12565 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12565 ⟨25,by decide⟩).lower ∧ (cell12565 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12565 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12565 ⟨26,by decide⟩).lower ∧ (cell12565 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12565 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12565 ⟨27,by decide⟩).lower ∧ (cell12565 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12565 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12565 ⟨28,by decide⟩).lower ∧ (cell12565 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12565 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12565 ⟨29,by decide⟩).lower ∧ (cell12565 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12565 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12565 ⟨30,by decide⟩).lower ∧ (cell12565 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12565 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12565 ⟨31,by decide⟩).lower ∧ (cell12565 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12565 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12565 ⟨32,by decide⟩).lower ∧ (cell12565 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12565 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12565 ⟨33,by decide⟩).lower ∧ (cell12565 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12565 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12565 ⟨34,by decide⟩).lower ∧ (cell12565 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12565 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12565 ⟨35,by decide⟩).lower ∧ (cell12565 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12565 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12565 ⟨36,by decide⟩).lower ∧ (cell12565 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12565 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12565 ⟨37,by decide⟩).lower ∧ (cell12565 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12565 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12565 ⟨38,by decide⟩).lower ∧ (cell12565 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12565 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12565 ⟨39,by decide⟩).lower ∧ (cell12565 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12565 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12565 ⟨40,by decide⟩).lower ∧ (cell12565 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12565 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12565 ⟨41,by decide⟩).lower ∧ (cell12565 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12565 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12565 ⟨42,by decide⟩).lower ∧ (cell12565 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12565 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12565 ⟨43,by decide⟩).lower ∧ (cell12565 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12565 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12565 ⟨44,by decide⟩).lower ∧ (cell12565 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12565 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12565 ⟨45,by decide⟩).lower ∧ (cell12565 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12565 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12565 ⟨46,by decide⟩).lower ∧ (cell12565 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12565 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12565 ⟨47,by decide⟩).lower ∧ (cell12565 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12565 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12565 ⟨48,by decide⟩).lower ∧ (cell12565 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12565 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12565 ⟨49,by decide⟩).lower ∧ (cell12565 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12565 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12565 ⟨50,by decide⟩).lower ∧ (cell12565 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12565 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12565 ⟨51,by decide⟩).lower ∧ (cell12565 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12565 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12565 ⟨52,by decide⟩).lower ∧ (cell12565 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12565 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12565 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12565 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12565,cell12565,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12565 i).lower ∧
    (cell12565 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12565 i).upper ≤ (0.532 : ℝ) ∧
    (cell12565 i).centre ≤ (0.1 : ℝ) ∧ (cell12565 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12565 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12565 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12565

/-! The local source numeric instances at 12565 have no network premises. -/
namespace BstLean.Part269.N12565
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12565)
open BstLean.Part268 (cell12565)

noncomputable def sourceNumerics12565 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12565 (cell12565 i)
      scalarRow12565.M scalarRow12565.H scalarRow12565.xi := by
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
    energy_allowance := scalarRow12565.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12565]
    centre_nonneg := (scalarRow12565.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12565])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12565
/-! Actual 12566 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12566 ≤ (1.036001327793 : ℝ) := by
  have hr : (112.098171260730 : ℝ) ≤ √(12566 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.098171260730 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12566 12566 (11 / 1000) ≤
    (0.008527231600 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12566) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.098171260730 : ℝ) ≤ √(12566 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12566)
  have hdiv : K / √(12566 : ℝ) ≤ K / 112.098171260730 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.098171260730 ≤ (0.008527231600 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12566.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12566 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12566 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12566 := gPlus_lower 12566
end BstLean.Part269.N12566

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12566
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036001327792 : ℝ) ≤ wn 12566 := by
  have hn : √(12566 : ℝ) ≤ 112.098171260731 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12566 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.098171260731 ≤ 2 / √(12566 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254614063 : ℝ) ≤ rhoBar 12566 BstLean.Part154.csC ∧
    rhoBar 12566 BstLean.Part154.csC ≤ 0.000254614457 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036001327792 : ℝ) / (1.295212 * 12566) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036001327793 : ℝ) / (1.29521 * 12566) := by gcongr
      _ ≤ (0.000254614457 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12566 BstLean.Part154.csC) ≤ 0.001018522657 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12566 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) ≤ 0.000194476338 ∧
    cc1 (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) ≤ 0.000123746565 ∧
    cc2 (rhoBar 12566 BstLean.Part154.csC) ≤ 0.000071835805 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12566 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12566 BstLean.Part154.csC * nuR (rhoBar 12566 BstLean.Part154.csC)) ≤ 0.000509245121 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254614457 : ℝ) * 0.001018522657 := by gcongr
      _ ≤ (0.000509245121 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12566 BstLean.Part154.csC) * nuR (rhoBar 12566 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018522657 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12566 BstLean.Part154.csC) * rhoBar 12566 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254614457 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254614457 / 2 + 0.399 * 0.001018522657 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194476338 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509245121 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123746565 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254614457 / 1.414213562 := by gcongr
      _ ≤ (0.000071835805 : ℝ) := by norm_num

end BstLean.Part269.N12566

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12566
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) ≤ 1.63331E-7 := by
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12566 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12566 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194476338 : ℝ) ^ 2 + 0.000123746565 ^ 2 + 3 * 0.000071835805 ^ 2 +
        2 * 0.797885 * 0.000194476338 * 0.000123746565 + 2 * 0.000194476338 * 0.000071835805 +
        4 * 0.797885 * 0.000123746565 * 0.000071835805 := by gcongr
    _ ≤ (1.63331E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12566 BstLean.Part154.csC Θ ≤ 0.002658315584 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12566 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12566 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036001327793 * 1.63331E-7 / (0.000254614063 : ℝ) := by gcongr
    _ ≤ 0.002658315584 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12566 BstLean.Part154.csC Θ ≤ 0.002950090431 + 0.000671712726 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12566 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036001327793 : ℝ) * ((2 * Θ * 0.000254614457 +
        (6863 / 10000) * 0.000254614457 * 12566 * 0.001018522657) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002950090431 + 0.000671712726 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12566 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12566 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12566 0.011 Θ ∧ gammaRatio 12566 0.011 Θ ≤ 0.000087529867 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12566 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036001327793 : ℝ) * 0.525 / ((1 - 0.011) * 12566) := by gcongr
      _ ≤ (0.000087529867 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12566 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12566 0.011 Θ) :=
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
    badAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12566 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12566 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12566 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12566 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12566 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12566 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12566 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12566 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12566 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12566 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036001327793 : ℝ) * 12566 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003693831171 + 0.003330028310 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12566

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12566
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12566 BstLean.Part154.csC) (piBar (rhoBar 12566 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12566 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12566 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12566 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12566 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12566 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12566 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12566 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12566 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12566 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052766451555 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12566) ≤ 0.010653497445 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12566 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036001327793)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010653497445 + 2 * 0.737676 / 12566) := by gcongr
    _ ≤ (0.052766451555 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12566 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12566

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12566
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497443792 : ℝ) ≤ plow 12566 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12566) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948696034)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395615682) : eMP 12566 0.011 xi bn ≤ 0.001201315765 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12566 : ℝ) * (1 - 0.011))) ≤ 0.000593965483 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395615682 / (12566 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593965483 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593965483 : ℝ) + 3.141593 * 0.052948696034 / (12566 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201315765 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948696034)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395615682) : PiBarMP 12566 12 0.011 xi bn ≤ 0.162117488222 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12566 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037357940013 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.479926444180 : ℝ) ≤ √((12566 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.098171260730 : ℝ) ≤ √(12566 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12566) ≤ 0.124287560681 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037357940013 + 0.052948696034 * 1.772454 / (2 * (111.479926444180 : ℝ))) * (1 + 0.001201315765) +
        8 / (12566 * 112.098171260730) + 0.124287560681 := by gcongr
    _ ≤ (0.162117488222 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948696034)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395615682) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282872288148) :
    parallelOracle 12566 0.011 xi bn cd ≤ 0.163119189614 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12566 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12566 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497443792 : ℝ) ≤ plow 12566 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.098171260730 : ℝ) ≤ √(12566 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282872288148 : ℝ) / (2 * 0.560497443792 * 112.098171260730)) * 0.162117488222 +
        0.282872288148 ^ 2 / (2 * 0.560497443792 * 112.098171260730) := by gcongr
    _ ≤ (0.163119189614 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948696034) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395615682)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282872288148) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12566 12566 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497443792 : ℝ) ≤ plow 12566 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.098171260730 : ℝ) ≤ √(12566 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12566 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12566 Θ 1.22 ≤ 0.011829813860 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.098171260730 := by gcongr <;> linarith
      _ ≤ (0.011829813860 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12566 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12566 12566 0.011 ≤ 0.008527231600 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12566 12566 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12566 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12566 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12566 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12566 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163119189614 + 0.011829813860 + (0.008527231600 : ℝ) *
        (1 + 2 * (0.282872288148 + 0.011829813860) / (0.560497443792 * 112.098171260730))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12566]

end BstLean.Part269.N12566

/-! The original eight local profiles supply actual 12566 moment certificates. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12566 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052948696034 ∧
    0 ≤ bN 12566 BstLean.Part154.csC (groupTheta g) ∧ bN 12566 BstLean.Part154.csC (groupTheta g) ≤ 0.001395615682 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12566 12566 0.011
      (momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12566 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12566 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12566 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230105836593 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12566 0.011
      (momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12566 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12566
/-! The actual computed-centre upper energy formula at 12566. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12566

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12566)
open BstLean.Part268 (cell12566)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085891231345
  | 2 => 0.086841583801
  | 3 => 0.087791222739
  | 4 => 0.088741827604
  | 5 => 0.089695420654
  | 6 => 0.090654416685
  | 7 => 0.091621677202
  | 8 => 0.092600569064
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12566 12566 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12566 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12566

/-! Actual upper energy certificates on all 43 source endpoints at 12566. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12566)
open BstLean.Part268 (cell12566)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12566 (gMinus 12566) (1 - (cell12566 i).lower) ≤ 1 ∧
    energyUpper 12566 (gMinus 12566) (BstLean.Part211.gPlus 12566)
      (finiteEnergy 12566 12566 0.011) (1 - (cell12566 i).lower) ≤
      (cell12566 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨10,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨11,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨12,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨13,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨14,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨15,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨16,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨17,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨18,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨19,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨20,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨21,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨22,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨23,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨24,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨25,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨26,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨27,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨28,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨29,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨30,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨31,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨32,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨33,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨34,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨35,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨36,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨37,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨38,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨39,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨40,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨41,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨42,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨43,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨44,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨45,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨46,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨47,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨48,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨49,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨50,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨51,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12566) (by norm_num)
        (q := 1 - (cell12566 ⟨52,by decide⟩).lower)
        (by norm_num [cell12566]) (by norm_num [cell12566])
      exact ⟨E.1,E.2.trans (by norm_num [cell12566])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12566

/-! Source-cell containment and simple scalar guards at 12566. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12566)
open BstLean.Part268 (cell12566)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12566 ⟨10,by decide⟩).lower ∧ (cell12566 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12566 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12566 ⟨11,by decide⟩).lower ∧ (cell12566 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12566 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12566 ⟨12,by decide⟩).lower ∧ (cell12566 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12566 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12566 ⟨13,by decide⟩).lower ∧ (cell12566 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12566 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12566 ⟨14,by decide⟩).lower ∧ (cell12566 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12566 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12566 ⟨15,by decide⟩).lower ∧ (cell12566 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12566 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12566 ⟨16,by decide⟩).lower ∧ (cell12566 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12566 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12566 ⟨17,by decide⟩).lower ∧ (cell12566 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12566 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12566 ⟨18,by decide⟩).lower ∧ (cell12566 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12566 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12566 ⟨19,by decide⟩).lower ∧ (cell12566 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12566 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12566 ⟨20,by decide⟩).lower ∧ (cell12566 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12566 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12566 ⟨21,by decide⟩).lower ∧ (cell12566 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12566 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12566 ⟨22,by decide⟩).lower ∧ (cell12566 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12566 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12566 ⟨23,by decide⟩).lower ∧ (cell12566 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12566 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12566 ⟨24,by decide⟩).lower ∧ (cell12566 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12566 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12566 ⟨25,by decide⟩).lower ∧ (cell12566 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12566 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12566 ⟨26,by decide⟩).lower ∧ (cell12566 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12566 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12566 ⟨27,by decide⟩).lower ∧ (cell12566 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12566 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12566 ⟨28,by decide⟩).lower ∧ (cell12566 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12566 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12566 ⟨29,by decide⟩).lower ∧ (cell12566 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12566 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12566 ⟨30,by decide⟩).lower ∧ (cell12566 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12566 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12566 ⟨31,by decide⟩).lower ∧ (cell12566 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12566 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12566 ⟨32,by decide⟩).lower ∧ (cell12566 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12566 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12566 ⟨33,by decide⟩).lower ∧ (cell12566 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12566 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12566 ⟨34,by decide⟩).lower ∧ (cell12566 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12566 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12566 ⟨35,by decide⟩).lower ∧ (cell12566 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12566 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12566 ⟨36,by decide⟩).lower ∧ (cell12566 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12566 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12566 ⟨37,by decide⟩).lower ∧ (cell12566 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12566 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12566 ⟨38,by decide⟩).lower ∧ (cell12566 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12566 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12566 ⟨39,by decide⟩).lower ∧ (cell12566 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12566 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12566 ⟨40,by decide⟩).lower ∧ (cell12566 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12566 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12566 ⟨41,by decide⟩).lower ∧ (cell12566 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12566 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12566 ⟨42,by decide⟩).lower ∧ (cell12566 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12566 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12566 ⟨43,by decide⟩).lower ∧ (cell12566 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12566 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12566 ⟨44,by decide⟩).lower ∧ (cell12566 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12566 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12566 ⟨45,by decide⟩).lower ∧ (cell12566 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12566 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12566 ⟨46,by decide⟩).lower ∧ (cell12566 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12566 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12566 ⟨47,by decide⟩).lower ∧ (cell12566 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12566 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12566 ⟨48,by decide⟩).lower ∧ (cell12566 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12566 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12566 ⟨49,by decide⟩).lower ∧ (cell12566 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12566 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12566 ⟨50,by decide⟩).lower ∧ (cell12566 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12566 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12566 ⟨51,by decide⟩).lower ∧ (cell12566 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12566 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12566 ⟨52,by decide⟩).lower ∧ (cell12566 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12566 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12566 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12566 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12566,cell12566,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12566 i).lower ∧
    (cell12566 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12566 i).upper ≤ (0.532 : ℝ) ∧
    (cell12566 i).centre ≤ (0.1 : ℝ) ∧ (cell12566 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12566 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12566 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12566

/-! The local source numeric instances at 12566 have no network premises. -/
namespace BstLean.Part269.N12566
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12566)
open BstLean.Part268 (cell12566)

noncomputable def sourceNumerics12566 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12566 (cell12566 i)
      scalarRow12566.M scalarRow12566.H scalarRow12566.xi := by
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
    energy_allowance := scalarRow12566.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12566]
    centre_nonneg := (scalarRow12566.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12566])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12566
/-! Actual 12567 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12567 ≤ (1.035999882724 : ℝ) := by
  have hr : (112.102631548059 : ℝ) ≤ √(12567 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.102631548059 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12567 12567 (11 / 1000) ≤
    (0.008526892320 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12567) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.102631548059 : ℝ) ≤ √(12567 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12567)
  have hdiv : K / √(12567 : ℝ) ≤ K / 112.102631548059 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.102631548059 ≤ (0.008526892320 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12567.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12567 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12567 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12567 := gPlus_lower 12567
end BstLean.Part269.N12567

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12567
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035999882723 : ℝ) ≤ wn 12567 := by
  have hn : √(12567 : ℝ) ≤ 112.102631548060 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12567 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.102631548060 ≤ 2 / √(12567 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254593448 : ℝ) ≤ rhoBar 12567 BstLean.Part154.csC ∧
    rhoBar 12567 BstLean.Part154.csC ≤ 0.000254593842 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035999882723 : ℝ) / (1.295212 * 12567) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035999882724 : ℝ) / (1.29521 * 12567) := by gcongr
      _ ≤ (0.000254593842 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12567 BstLean.Part154.csC) ≤ 0.001018440187 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12567 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) ≤ 0.000194460592 ∧
    cc1 (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) ≤ 0.000123736546 ∧
    cc2 (rhoBar 12567 BstLean.Part154.csC) ≤ 0.000071829988 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12567 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12567 BstLean.Part154.csC * nuR (rhoBar 12567 BstLean.Part154.csC)) ≤ 0.000509203889 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254593842 : ℝ) * 0.001018440187 := by gcongr
      _ ≤ (0.000509203889 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12567 BstLean.Part154.csC) * nuR (rhoBar 12567 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018440187 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12567 BstLean.Part154.csC) * rhoBar 12567 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254593842 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254593842 / 2 + 0.399 * 0.001018440187 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194460592 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509203889 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123736546 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254593842 / 1.414213562 := by gcongr
      _ ≤ (0.000071829988 : ℝ) := by norm_num

end BstLean.Part269.N12567

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12567
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) ≤ 1.63305E-7 := by
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12567 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12567 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194460592 : ℝ) ^ 2 + 0.000123736546 ^ 2 + 3 * 0.000071829988 ^ 2 +
        2 * 0.797885 * 0.000194460592 * 0.000123736546 + 2 * 0.000194460592 * 0.000071829988 +
        4 * 0.797885 * 0.000123736546 * 0.000071829988 := by gcongr
    _ ≤ (1.63305E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12567 BstLean.Part154.csC Θ ≤ 0.002658103925 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12567 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12567 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035999882724 * 1.63305E-7 / (0.000254593448 : ℝ) := by gcongr
    _ ≤ 0.002658103925 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12567 BstLean.Part154.csC Θ ≤ 0.002949843340 + 0.000671657403 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12567 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035999882724 : ℝ) * ((2 * Θ * 0.000254593842 +
        (6863 / 10000) * 0.000254593842 * 12567 * 0.001018440187) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002949843340 + 0.000671657403 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12567 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12567 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12567 0.011 Θ ∧ gammaRatio 12567 0.011 Θ ≤ 0.000087522779 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12567 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035999882724 : ℝ) * 0.525 / ((1 - 0.011) * 12567) := by gcongr
      _ ≤ (0.000087522779 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12567 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12567 0.011 Θ) :=
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
    badAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12567 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12567 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12567 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12567 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12567 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12567 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12567 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12567 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12567 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12567 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035999882724 : ℝ) * 12567 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003693584080 + 0.003329761328 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12567

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12567
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12567 BstLean.Part154.csC) (piBar (rhoBar 12567 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12567 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12567 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12567 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12567 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12567 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12567 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12567 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12567 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12567 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052764329226 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12567) ≤ 0.010653073569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12567 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035999882724)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010653073569 + 2 * 0.737676 / 12567) := by gcongr
    _ ≤ (0.052764329226 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12567 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12567

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12567
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497489981 : ℝ) ≤ plow 12567 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12567) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948308778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395504561) : eMP 12567 0.011 xi bn ≤ 0.001201220046 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12567 : ℝ) * (1 - 0.011))) ≤ 0.000593918205 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395504561 / (12567 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593918205 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593918205 : ℝ) + 3.141593 * 0.052948308778 / (12567 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201220046 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948308778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395504561) : PiBarMP 12567 12 0.011 xi bn ≤ 0.162111029918 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12567 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037356452736 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.484362132094 : ℝ) ≤ √((12567 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.102631548059 : ℝ) ≤ √(12567 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12567) ≤ 0.124282615585 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037356452736 + 0.052948308778 * 1.772454 / (2 * (111.484362132094 : ℝ))) * (1 + 0.001201220046) +
        8 / (12567 * 112.102631548059) + 0.124282615585 := by gcongr
    _ ≤ (0.162111029918 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948308778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395504561) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282869324344) :
    parallelOracle 12567 0.011 xi bn cd ≤ 0.163112659668 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12567 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12567 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497489981 : ℝ) ≤ plow 12567 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.102631548059 : ℝ) ≤ √(12567 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282869324344 : ℝ) / (2 * 0.560497489981 * 112.102631548059)) * 0.162111029918 +
        0.282869324344 ^ 2 / (2 * 0.560497489981 * 112.102631548059) := by gcongr
    _ ≤ (0.163112659668 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052948308778) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395504561)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282869324344) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12567 12567 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497489981 : ℝ) ≤ plow 12567 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.102631548059 : ℝ) ≤ √(12567 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12567 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12567 Θ 1.22 ≤ 0.011829343181 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.102631548059 := by gcongr <;> linarith
      _ ≤ (0.011829343181 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12567 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12567 12567 0.011 ≤ 0.008526892320 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12567 12567 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12567 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12567 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12567 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12567 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163112659668 + 0.011829343181 + (0.008526892320 : ℝ) *
        (1 + 2 * (0.282869324344 + 0.011829343181) / (0.560497489981 * 112.102631548059))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12567]

end BstLean.Part269.N12567

/-! The original eight local profiles supply actual 12567 moment certificates. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12567 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052948308778 ∧
    0 ≤ bN 12567 BstLean.Part154.csC (groupTheta g) ∧ bN 12567 BstLean.Part154.csC (groupTheta g) ≤ 0.001395504561 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12567 12567 0.011
      (momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12567 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12567 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12567 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230104995118 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12567 0.011
      (momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12567 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12567
/-! The actual computed-centre upper energy formula at 12567. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12567

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12567)
open BstLean.Part268 (cell12567)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085888159973
  | 2 => 0.086838452364
  | 3 => 0.087788021899
  | 4 => 0.088738545915
  | 5 => 0.089692044199
  | 6 => 0.090650928666
  | 7 => 0.091618057488
  | 8 => 0.092596793688
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12567 12567 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12567 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12567

/-! Actual upper energy certificates on all 43 source endpoints at 12567. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12567)
open BstLean.Part268 (cell12567)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12567 (gMinus 12567) (1 - (cell12567 i).lower) ≤ 1 ∧
    energyUpper 12567 (gMinus 12567) (BstLean.Part211.gPlus 12567)
      (finiteEnergy 12567 12567 0.011) (1 - (cell12567 i).lower) ≤
      (cell12567 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨10,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨11,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨12,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨13,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨14,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨15,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨16,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨17,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨18,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨19,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨20,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨21,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨22,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨23,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨24,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨25,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨26,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨27,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨28,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨29,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨30,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨31,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨32,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨33,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨34,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨35,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨36,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨37,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨38,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨39,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨40,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨41,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨42,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨43,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨44,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨45,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨46,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨47,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨48,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨49,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨50,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨51,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12567) (by norm_num)
        (q := 1 - (cell12567 ⟨52,by decide⟩).lower)
        (by norm_num [cell12567]) (by norm_num [cell12567])
      exact ⟨E.1,E.2.trans (by norm_num [cell12567])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12567

/-! Source-cell containment and simple scalar guards at 12567. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12567)
open BstLean.Part268 (cell12567)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12567 ⟨10,by decide⟩).lower ∧ (cell12567 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12567 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12567 ⟨11,by decide⟩).lower ∧ (cell12567 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12567 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12567 ⟨12,by decide⟩).lower ∧ (cell12567 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12567 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12567 ⟨13,by decide⟩).lower ∧ (cell12567 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12567 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12567 ⟨14,by decide⟩).lower ∧ (cell12567 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12567 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12567 ⟨15,by decide⟩).lower ∧ (cell12567 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12567 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12567 ⟨16,by decide⟩).lower ∧ (cell12567 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12567 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12567 ⟨17,by decide⟩).lower ∧ (cell12567 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12567 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12567 ⟨18,by decide⟩).lower ∧ (cell12567 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12567 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12567 ⟨19,by decide⟩).lower ∧ (cell12567 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12567 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12567 ⟨20,by decide⟩).lower ∧ (cell12567 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12567 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12567 ⟨21,by decide⟩).lower ∧ (cell12567 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12567 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12567 ⟨22,by decide⟩).lower ∧ (cell12567 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12567 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12567 ⟨23,by decide⟩).lower ∧ (cell12567 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12567 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12567 ⟨24,by decide⟩).lower ∧ (cell12567 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12567 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12567 ⟨25,by decide⟩).lower ∧ (cell12567 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12567 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12567 ⟨26,by decide⟩).lower ∧ (cell12567 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12567 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12567 ⟨27,by decide⟩).lower ∧ (cell12567 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12567 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12567 ⟨28,by decide⟩).lower ∧ (cell12567 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12567 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12567 ⟨29,by decide⟩).lower ∧ (cell12567 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12567 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12567 ⟨30,by decide⟩).lower ∧ (cell12567 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12567 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12567 ⟨31,by decide⟩).lower ∧ (cell12567 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12567 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12567 ⟨32,by decide⟩).lower ∧ (cell12567 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12567 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12567 ⟨33,by decide⟩).lower ∧ (cell12567 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12567 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12567 ⟨34,by decide⟩).lower ∧ (cell12567 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12567 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12567 ⟨35,by decide⟩).lower ∧ (cell12567 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12567 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12567 ⟨36,by decide⟩).lower ∧ (cell12567 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12567 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12567 ⟨37,by decide⟩).lower ∧ (cell12567 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12567 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12567 ⟨38,by decide⟩).lower ∧ (cell12567 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12567 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12567 ⟨39,by decide⟩).lower ∧ (cell12567 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12567 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12567 ⟨40,by decide⟩).lower ∧ (cell12567 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12567 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12567 ⟨41,by decide⟩).lower ∧ (cell12567 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12567 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12567 ⟨42,by decide⟩).lower ∧ (cell12567 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12567 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12567 ⟨43,by decide⟩).lower ∧ (cell12567 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12567 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12567 ⟨44,by decide⟩).lower ∧ (cell12567 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12567 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12567 ⟨45,by decide⟩).lower ∧ (cell12567 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12567 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12567 ⟨46,by decide⟩).lower ∧ (cell12567 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12567 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12567 ⟨47,by decide⟩).lower ∧ (cell12567 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12567 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12567 ⟨48,by decide⟩).lower ∧ (cell12567 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12567 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12567 ⟨49,by decide⟩).lower ∧ (cell12567 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12567 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12567 ⟨50,by decide⟩).lower ∧ (cell12567 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12567 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12567 ⟨51,by decide⟩).lower ∧ (cell12567 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12567 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12567 ⟨52,by decide⟩).lower ∧ (cell12567 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12567 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12567 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12567 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12567,cell12567,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12567 i).lower ∧
    (cell12567 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12567 i).upper ≤ (0.532 : ℝ) ∧
    (cell12567 i).centre ≤ (0.1 : ℝ) ∧ (cell12567 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12567 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12567 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12567

/-! The local source numeric instances at 12567 have no network premises. -/
namespace BstLean.Part269.N12567
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12567)
open BstLean.Part268 (cell12567)

noncomputable def sourceNumerics12567 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12567 (cell12567 i)
      scalarRow12567.M scalarRow12567.H scalarRow12567.xi := by
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
    energy_allowance := scalarRow12567.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12567]
    centre_nonneg := (scalarRow12567.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12567])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12567
/-! Actual 12568 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12568 ≤ (1.035998437829 : ℝ) := by
  have hr : (112.107091657932 : ℝ) ≤ √(12568 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.107091657932 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12568 12568 (11 / 1000) ≤
    (0.008526553080 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12568) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.107091657932 : ℝ) ≤ √(12568 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12568)
  have hdiv : K / √(12568 : ℝ) ≤ K / 112.107091657932 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.107091657932 ≤ (0.008526553080 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12568.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12568 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12568 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12568 := gPlus_lower 12568
end BstLean.Part269.N12568

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12568
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035998437828 : ℝ) ≤ wn 12568 := by
  have hn : √(12568 : ℝ) ≤ 112.107091657933 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12568 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.107091657933 ≤ 2 / √(12568 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254572835 : ℝ) ≤ rhoBar 12568 BstLean.Part154.csC ∧
    rhoBar 12568 BstLean.Part154.csC ≤ 0.000254573229 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035998437828 : ℝ) / (1.295212 * 12568) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035998437829 : ℝ) / (1.29521 * 12568) := by gcongr
      _ ≤ (0.000254573229 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12568 BstLean.Part154.csC) ≤ 0.001018357724 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12568 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) ≤ 0.000194444846 ∧
    cc1 (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) ≤ 0.000123726527 ∧
    cc2 (rhoBar 12568 BstLean.Part154.csC) ≤ 0.000071824173 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12568 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12568 BstLean.Part154.csC * nuR (rhoBar 12568 BstLean.Part154.csC)) ≤ 0.000509162660 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254573229 : ℝ) * 0.001018357724 := by gcongr
      _ ≤ (0.000509162660 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12568 BstLean.Part154.csC) * nuR (rhoBar 12568 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018357724 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12568 BstLean.Part154.csC) * rhoBar 12568 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254573229 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254573229 / 2 + 0.399 * 0.001018357724 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194444846 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509162660 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123726527 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254573229 / 1.414213562 := by gcongr
      _ ≤ (0.000071824173 : ℝ) := by norm_num

end BstLean.Part269.N12568

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12568
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) ≤ 1.63278E-7 := by
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12568 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12568 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194444846 : ℝ) ^ 2 + 0.000123726527 ^ 2 + 3 * 0.000071824173 ^ 2 +
        2 * 0.797885 * 0.000194444846 * 0.000123726527 + 2 * 0.000194444846 * 0.000071824173 +
        4 * 0.797885 * 0.000123726527 * 0.000071824173 := by gcongr
    _ ≤ (1.63278E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12568 BstLean.Part154.csC Θ ≤ 0.002657875935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12568 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12568 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035998437829 * 1.63278E-7 / (0.000254572835 : ℝ) := by gcongr
    _ ≤ 0.002657875935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12568 BstLean.Part154.csC Θ ≤ 0.002949596257 + 0.000671602086 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12568 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035998437829 : ℝ) * ((2 * Θ * 0.000254573229 +
        (6863 / 10000) * 0.000254573229 * 12568 * 0.001018357724) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002949596257 + 0.000671602086 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12568 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12568 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12568 0.011 Θ ∧ gammaRatio 12568 0.011 Θ ≤ 0.000087515693 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12568 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035998437829 : ℝ) * 0.525 / ((1 - 0.011) * 12568) := by gcongr
      _ ≤ (0.000087515693 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12568 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12568 0.011 Θ) :=
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
    badAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12568 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12568 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12568 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12568 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12568 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12568 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12568 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12568 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12568 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12568 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035998437829 : ℝ) * 12568 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003693336997 + 0.003329478021 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12568

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12568
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12568 BstLean.Part154.csC) (piBar (rhoBar 12568 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12568 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12568 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12568 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12568 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12568 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12568 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12568 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12568 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12568 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052762207149 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12568) ≤ 0.010652649743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12568 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035998437829)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010652649743 + 2 * 0.737676 / 12568) := by gcongr
    _ ≤ (0.052762207149 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12568 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12568

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12568
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497536163 : ℝ) ≤ plow 12568 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12568) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947912959)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395384866) : eMP 12568 0.011 xi bn ≤ 0.001201120683 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12568 : ℝ) * (1 - 0.011))) ≤ 0.000593869106 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395384866 / (12568 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593869106 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593869106 : ℝ) + 3.141593 * 0.052947912959 / (12568 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201120683 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947912959)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395384866) : PiBarMP 12568 12 0.011 xi bn ≤ 0.162104457042 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12568 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037354850636 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.488797643530 : ℝ) ≤ √((12568 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.107091657932 : ℝ) ≤ √(12568 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12568) ≤ 0.124277671080 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037354850636 + 0.052947912959 * 1.772454 / (2 * (111.488797643530 : ℝ))) * (1 + 0.001201120683) +
        8 / (12568 * 112.107091657932) + 0.124277671080 := by gcongr
    _ ≤ (0.162104457042 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947912959)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395384866) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282866342182) :
    parallelOracle 12568 0.011 xi bn cd ≤ 0.163106014795 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12568 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12568 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497536163 : ℝ) ≤ plow 12568 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.107091657932 : ℝ) ≤ √(12568 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282866342182 : ℝ) / (2 * 0.560497536163 * 112.107091657932)) * 0.162104457042 +
        0.282866342182 ^ 2 / (2 * 0.560497536163 * 112.107091657932) := by gcongr
    _ ≤ (0.163106014795 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947912959) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395384866)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282866342182) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12568 12568 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497536163 : ℝ) ≤ plow 12568 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.107091657932 : ℝ) ≤ √(12568 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12568 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12568 Θ 1.22 ≤ 0.011828872558 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.107091657932 := by gcongr <;> linarith
      _ ≤ (0.011828872558 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12568 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12568 12568 0.011 ≤ 0.008526553080 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12568 12568 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12568 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12568 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12568 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12568 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163106014795 + 0.011828872558 + (0.008526553080 : ℝ) *
        (1 + 2 * (0.282866342182 + 0.011828872558) / (0.560497536163 * 112.107091657932))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12568]

end BstLean.Part269.N12568

/-! The original eight local profiles supply actual 12568 moment certificates. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12568 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052947912959 ∧
    0 ≤ bN 12568 BstLean.Part154.csC (groupTheta g) ∧ bN 12568 BstLean.Part154.csC (groupTheta g) ≤ 0.001395384866 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12568 12568 0.011
      (momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12568 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12568 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12568 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230104135033 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12568 0.011
      (momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12568 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12568
/-! The actual computed-centre upper energy formula at 12568. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12568

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12568)
open BstLean.Part268 (cell12568)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085885089844
  | 2 => 0.086835322223
  | 3 => 0.087784822420
  | 4 => 0.088735265667
  | 5 => 0.089688669283
  | 6 => 0.090647442305
  | 7 => 0.091614439576
  | 8 => 0.092593020287
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12568 12568 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12568 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12568

/-! Actual upper energy certificates on all 43 source endpoints at 12568. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12568)
open BstLean.Part268 (cell12568)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12568 (gMinus 12568) (1 - (cell12568 i).lower) ≤ 1 ∧
    energyUpper 12568 (gMinus 12568) (BstLean.Part211.gPlus 12568)
      (finiteEnergy 12568 12568 0.011) (1 - (cell12568 i).lower) ≤
      (cell12568 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨10,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨11,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨12,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨13,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨14,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨15,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨16,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨17,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨18,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨19,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨20,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨21,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨22,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨23,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨24,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨25,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨26,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨27,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨28,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨29,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨30,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨31,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨32,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨33,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨34,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨35,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨36,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨37,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨38,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨39,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨40,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨41,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨42,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨43,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨44,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨45,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨46,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨47,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨48,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨49,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨50,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨51,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12568) (by norm_num)
        (q := 1 - (cell12568 ⟨52,by decide⟩).lower)
        (by norm_num [cell12568]) (by norm_num [cell12568])
      exact ⟨E.1,E.2.trans (by norm_num [cell12568])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12568

/-! Source-cell containment and simple scalar guards at 12568. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12568)
open BstLean.Part268 (cell12568)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12568 ⟨10,by decide⟩).lower ∧ (cell12568 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12568 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12568 ⟨11,by decide⟩).lower ∧ (cell12568 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12568 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12568 ⟨12,by decide⟩).lower ∧ (cell12568 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12568 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12568 ⟨13,by decide⟩).lower ∧ (cell12568 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12568 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12568 ⟨14,by decide⟩).lower ∧ (cell12568 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12568 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12568 ⟨15,by decide⟩).lower ∧ (cell12568 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12568 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12568 ⟨16,by decide⟩).lower ∧ (cell12568 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12568 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12568 ⟨17,by decide⟩).lower ∧ (cell12568 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12568 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12568 ⟨18,by decide⟩).lower ∧ (cell12568 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12568 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12568 ⟨19,by decide⟩).lower ∧ (cell12568 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12568 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12568 ⟨20,by decide⟩).lower ∧ (cell12568 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12568 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12568 ⟨21,by decide⟩).lower ∧ (cell12568 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12568 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12568 ⟨22,by decide⟩).lower ∧ (cell12568 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12568 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12568 ⟨23,by decide⟩).lower ∧ (cell12568 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12568 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12568 ⟨24,by decide⟩).lower ∧ (cell12568 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12568 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12568 ⟨25,by decide⟩).lower ∧ (cell12568 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12568 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12568 ⟨26,by decide⟩).lower ∧ (cell12568 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12568 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12568 ⟨27,by decide⟩).lower ∧ (cell12568 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12568 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12568 ⟨28,by decide⟩).lower ∧ (cell12568 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12568 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12568 ⟨29,by decide⟩).lower ∧ (cell12568 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12568 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12568 ⟨30,by decide⟩).lower ∧ (cell12568 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12568 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12568 ⟨31,by decide⟩).lower ∧ (cell12568 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12568 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12568 ⟨32,by decide⟩).lower ∧ (cell12568 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12568 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12568 ⟨33,by decide⟩).lower ∧ (cell12568 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12568 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12568 ⟨34,by decide⟩).lower ∧ (cell12568 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12568 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12568 ⟨35,by decide⟩).lower ∧ (cell12568 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12568 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12568 ⟨36,by decide⟩).lower ∧ (cell12568 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12568 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12568 ⟨37,by decide⟩).lower ∧ (cell12568 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12568 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12568 ⟨38,by decide⟩).lower ∧ (cell12568 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12568 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12568 ⟨39,by decide⟩).lower ∧ (cell12568 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12568 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12568 ⟨40,by decide⟩).lower ∧ (cell12568 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12568 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12568 ⟨41,by decide⟩).lower ∧ (cell12568 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12568 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12568 ⟨42,by decide⟩).lower ∧ (cell12568 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12568 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12568 ⟨43,by decide⟩).lower ∧ (cell12568 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12568 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12568 ⟨44,by decide⟩).lower ∧ (cell12568 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12568 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12568 ⟨45,by decide⟩).lower ∧ (cell12568 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12568 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12568 ⟨46,by decide⟩).lower ∧ (cell12568 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12568 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12568 ⟨47,by decide⟩).lower ∧ (cell12568 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12568 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12568 ⟨48,by decide⟩).lower ∧ (cell12568 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12568 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12568 ⟨49,by decide⟩).lower ∧ (cell12568 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12568 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12568 ⟨50,by decide⟩).lower ∧ (cell12568 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12568 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12568 ⟨51,by decide⟩).lower ∧ (cell12568 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12568 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12568 ⟨52,by decide⟩).lower ∧ (cell12568 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12568 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12568 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12568 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12568,cell12568,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12568 i).lower ∧
    (cell12568 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12568 i).upper ≤ (0.532 : ℝ) ∧
    (cell12568 i).centre ≤ (0.1 : ℝ) ∧ (cell12568 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12568 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12568 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12568

/-! The local source numeric instances at 12568 have no network premises. -/
namespace BstLean.Part269.N12568
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12568)
open BstLean.Part268 (cell12568)

noncomputable def sourceNumerics12568 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12568 (cell12568 i)
      scalarRow12568.M scalarRow12568.H scalarRow12568.xi := by
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
    energy_allowance := scalarRow12568.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12568]
    centre_nonneg := (scalarRow12568.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12568])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12568
/-! Actual 12569 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12569 ≤ (1.035996993107 : ℝ) := by
  have hr : (112.111551590369 : ℝ) ≤ √(12569 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.111551590369 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12569 12569 (11 / 1000) ≤
    (0.008526213881 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12569) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.111551590369 : ℝ) ≤ √(12569 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12569)
  have hdiv : K / √(12569 : ℝ) ≤ K / 112.111551590369 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.111551590369 ≤ (0.008526213881 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12569.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12569 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12569 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12569 := gPlus_lower 12569
end BstLean.Part269.N12569

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12569
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035996993106 : ℝ) ≤ wn 12569 := by
  have hn : √(12569 : ℝ) ≤ 112.111551590370 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12569 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.111551590370 ≤ 2 / √(12569 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254552226 : ℝ) ≤ rhoBar 12569 BstLean.Part154.csC ∧
    rhoBar 12569 BstLean.Part154.csC ≤ 0.000254552620 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035996993106 : ℝ) / (1.295212 * 12569) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035996993107 : ℝ) / (1.29521 * 12569) := by gcongr
      _ ≤ (0.000254552620 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12569 BstLean.Part154.csC) ≤ 0.001018275278 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12569 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) ≤ 0.000194429104 ∧
    cc1 (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) ≤ 0.000123716510 ∧
    cc2 (rhoBar 12569 BstLean.Part154.csC) ≤ 0.000071818358 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12569 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12569 BstLean.Part154.csC * nuR (rhoBar 12569 BstLean.Part154.csC)) ≤ 0.000509121440 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254552620 : ℝ) * 0.001018275278 := by gcongr
      _ ≤ (0.000509121440 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12569 BstLean.Part154.csC) * nuR (rhoBar 12569 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018275278 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12569 BstLean.Part154.csC) * rhoBar 12569 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254552620 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254552620 / 2 + 0.399 * 0.001018275278 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194429104 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509121440 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123716510 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254552620 / 1.414213562 := by gcongr
      _ ≤ (0.000071818358 : ℝ) := by norm_num

end BstLean.Part269.N12569

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12569
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) ≤ 1.63252E-7 := by
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12569 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12569 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194429104 : ℝ) ^ 2 + 0.000123716510 ^ 2 + 3 * 0.000071818358 ^ 2 +
        2 * 0.797885 * 0.000194429104 * 0.000123716510 + 2 * 0.000194429104 * 0.000071818358 +
        4 * 0.797885 * 0.000123716510 * 0.000071818358 := by gcongr
    _ ≤ (1.63252E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12569 BstLean.Part154.csC Θ ≤ 0.002657664147 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12569 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12569 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035996993107 * 1.63252E-7 / (0.000254552226 : ℝ) := by gcongr
    _ ≤ 0.002657664147 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12569 BstLean.Part154.csC Θ ≤ 0.002949349233 + 0.000671546780 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12569 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035996993107 : ℝ) * ((2 * Θ * 0.000254552620 +
        (6863 / 10000) * 0.000254552620 * 12569 * 0.001018275278) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002949349233 + 0.000671546780 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12569 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12569 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12569 0.011 Θ ∧ gammaRatio 12569 0.011 Θ ≤ 0.000087508609 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12569 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035996993107 : ℝ) * 0.525 / ((1 - 0.011) * 12569) := by gcongr
      _ ≤ (0.000087508609 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12569 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12569 0.011 Θ) :=
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
    badAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12569 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12569 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12569 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12569 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12569 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12569 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12569 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12569 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12569 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12569 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035996993107 : ℝ) * 12569 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003693089973 + 0.003329210927 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12569

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12569
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12569 BstLean.Part154.csC) (piBar (rhoBar 12569 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12569 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12569 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12569 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12569 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12569 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12569 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12569 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12569 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12569 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052760085329 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12569) ≤ 0.010652225968 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12569 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035996993107)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010652225968 + 2 * 0.737676 / 12569) := by gcongr
    _ ≤ (0.052760085329 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12569 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12569

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12569
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497582337 : ℝ) ≤ plow 12569 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12569) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947525710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395273678) : eMP 12569 0.011 xi bn ≤ 0.001201024951 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12569 : ℝ) * (1 - 0.011))) ≤ 0.000593821821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395273678 / (12569 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593821821 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593821821 : ℝ) + 3.141593 * 0.052947525710 / (12569 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201024951 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947525710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395273678) : PiBarMP 12569 12 0.011 xi bn ≤ 0.162097998903 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12569 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037353362339 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.493232978508 : ℝ) ≤ √((12569 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.111551590369 : ℝ) ≤ √(12569 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12569) ≤ 0.124272727165 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037353362339 + 0.052947525710 * 1.772454 / (2 * (111.493232978508 : ℝ))) * (1 + 0.001201024951) +
        8 / (12569 * 112.111551590369) + 0.124272727165 := by gcongr
    _ ≤ (0.162097998903 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947525710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395273678) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282863378896) :
    parallelOracle 12569 0.011 xi bn cd ≤ 0.163099485033 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12569 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12569 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497582337 : ℝ) ≤ plow 12569 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.111551590369 : ℝ) ≤ √(12569 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282863378896 : ℝ) / (2 * 0.560497582337 * 112.111551590369)) * 0.162097998903 +
        0.282863378896 ^ 2 / (2 * 0.560497582337 * 112.111551590369) := by gcongr
    _ ≤ (0.163099485033 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947525710) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395273678)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282863378896) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12569 12569 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497582337 : ℝ) ≤ plow 12569 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.111551590369 : ℝ) ≤ √(12569 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12569 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12569 Θ 1.22 ≤ 0.011828401991 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.111551590369 := by gcongr <;> linarith
      _ ≤ (0.011828401991 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12569 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12569 12569 0.011 ≤ 0.008526213881 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12569 12569 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12569 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12569 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12569 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12569 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163099485033 + 0.011828401991 + (0.008526213881 : ℝ) *
        (1 + 2 * (0.282863378896 + 0.011828401991) / (0.560497582337 * 112.111551590369))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12569]

end BstLean.Part269.N12569

/-! The original eight local profiles supply actual 12569 moment certificates. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12569 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052947525710 ∧
    0 ≤ bN 12569 BstLean.Part154.csC (groupTheta g) ∧ bN 12569 BstLean.Part154.csC (groupTheta g) ≤ 0.001395273678 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12569 12569 0.011
      (momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12569 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12569 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12569 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230103293567 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12569 0.011
      (momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12569 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12569
/-! The actual computed-centre upper energy formula at 12569. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12569

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12569)
open BstLean.Part268 (cell12569)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085882020956
  | 2 => 0.086832193377
  | 3 => 0.087781624301
  | 4 => 0.088731986859
  | 5 => 0.089685295904
  | 6 => 0.090643957601
  | 7 => 0.091610823465
  | 8 => 0.092589248858
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12569 12569 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12569 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12569

/-! Actual upper energy certificates on all 43 source endpoints at 12569. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12569)
open BstLean.Part268 (cell12569)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12569 (gMinus 12569) (1 - (cell12569 i).lower) ≤ 1 ∧
    energyUpper 12569 (gMinus 12569) (BstLean.Part211.gPlus 12569)
      (finiteEnergy 12569 12569 0.011) (1 - (cell12569 i).lower) ≤
      (cell12569 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨10,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨11,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨12,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨13,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨14,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨15,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨16,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨17,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨18,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨19,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨20,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨21,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨22,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨23,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨24,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨25,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨26,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨27,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨28,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨29,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨30,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨31,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨32,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨33,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨34,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨35,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨36,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨37,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨38,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨39,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨40,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨41,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨42,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨43,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨44,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨45,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨46,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨47,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨48,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨49,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨50,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨51,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12569) (by norm_num)
        (q := 1 - (cell12569 ⟨52,by decide⟩).lower)
        (by norm_num [cell12569]) (by norm_num [cell12569])
      exact ⟨E.1,E.2.trans (by norm_num [cell12569])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12569

/-! Source-cell containment and simple scalar guards at 12569. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12569)
open BstLean.Part268 (cell12569)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12569 ⟨10,by decide⟩).lower ∧ (cell12569 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12569 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12569 ⟨11,by decide⟩).lower ∧ (cell12569 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12569 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12569 ⟨12,by decide⟩).lower ∧ (cell12569 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12569 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12569 ⟨13,by decide⟩).lower ∧ (cell12569 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12569 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12569 ⟨14,by decide⟩).lower ∧ (cell12569 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12569 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12569 ⟨15,by decide⟩).lower ∧ (cell12569 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12569 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12569 ⟨16,by decide⟩).lower ∧ (cell12569 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12569 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12569 ⟨17,by decide⟩).lower ∧ (cell12569 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12569 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12569 ⟨18,by decide⟩).lower ∧ (cell12569 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12569 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12569 ⟨19,by decide⟩).lower ∧ (cell12569 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12569 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12569 ⟨20,by decide⟩).lower ∧ (cell12569 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12569 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12569 ⟨21,by decide⟩).lower ∧ (cell12569 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12569 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12569 ⟨22,by decide⟩).lower ∧ (cell12569 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12569 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12569 ⟨23,by decide⟩).lower ∧ (cell12569 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12569 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12569 ⟨24,by decide⟩).lower ∧ (cell12569 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12569 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12569 ⟨25,by decide⟩).lower ∧ (cell12569 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12569 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12569 ⟨26,by decide⟩).lower ∧ (cell12569 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12569 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12569 ⟨27,by decide⟩).lower ∧ (cell12569 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12569 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12569 ⟨28,by decide⟩).lower ∧ (cell12569 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12569 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12569 ⟨29,by decide⟩).lower ∧ (cell12569 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12569 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12569 ⟨30,by decide⟩).lower ∧ (cell12569 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12569 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12569 ⟨31,by decide⟩).lower ∧ (cell12569 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12569 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12569 ⟨32,by decide⟩).lower ∧ (cell12569 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12569 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12569 ⟨33,by decide⟩).lower ∧ (cell12569 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12569 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12569 ⟨34,by decide⟩).lower ∧ (cell12569 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12569 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12569 ⟨35,by decide⟩).lower ∧ (cell12569 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12569 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12569 ⟨36,by decide⟩).lower ∧ (cell12569 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12569 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12569 ⟨37,by decide⟩).lower ∧ (cell12569 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12569 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12569 ⟨38,by decide⟩).lower ∧ (cell12569 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12569 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12569 ⟨39,by decide⟩).lower ∧ (cell12569 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12569 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12569 ⟨40,by decide⟩).lower ∧ (cell12569 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12569 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12569 ⟨41,by decide⟩).lower ∧ (cell12569 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12569 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12569 ⟨42,by decide⟩).lower ∧ (cell12569 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12569 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12569 ⟨43,by decide⟩).lower ∧ (cell12569 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12569 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12569 ⟨44,by decide⟩).lower ∧ (cell12569 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12569 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12569 ⟨45,by decide⟩).lower ∧ (cell12569 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12569 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12569 ⟨46,by decide⟩).lower ∧ (cell12569 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12569 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12569 ⟨47,by decide⟩).lower ∧ (cell12569 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12569 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12569 ⟨48,by decide⟩).lower ∧ (cell12569 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12569 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12569 ⟨49,by decide⟩).lower ∧ (cell12569 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12569 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12569 ⟨50,by decide⟩).lower ∧ (cell12569 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12569 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12569 ⟨51,by decide⟩).lower ∧ (cell12569 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12569 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12569 ⟨52,by decide⟩).lower ∧ (cell12569 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12569 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12569 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12569 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12569,cell12569,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12569 i).lower ∧
    (cell12569 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12569 i).upper ≤ (0.532 : ℝ) ∧
    (cell12569 i).centre ≤ (0.1 : ℝ) ∧ (cell12569 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12569 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12569 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12569

/-! The local source numeric instances at 12569 have no network premises. -/
namespace BstLean.Part269.N12569
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12569)
open BstLean.Part268 (cell12569)

noncomputable def sourceNumerics12569 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12569 (cell12569 i)
      scalarRow12569.M scalarRow12569.H scalarRow12569.xi := by
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
    energy_allowance := scalarRow12569.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12569]
    centre_nonneg := (scalarRow12569.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12569])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12569
/-! Actual 12570 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12570 ≤ (1.035995548559 : ℝ) := by
  have hr : (112.116011345391 : ℝ) ≤ √(12570 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.116011345391 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12570 12570 (11 / 1000) ≤
    (0.008525874723 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12570) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.116011345391 : ℝ) ≤ √(12570 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12570)
  have hdiv : K / √(12570 : ℝ) ≤ K / 112.116011345391 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.116011345391 ≤ (0.008525874723 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12570.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12570 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12570 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12570 := gPlus_lower 12570
end BstLean.Part269.N12570

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12570
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035995548558 : ℝ) ≤ wn 12570 := by
  have hn : √(12570 : ℝ) ≤ 112.116011345392 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12570 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.116011345392 ≤ 2 / √(12570 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254531621 : ℝ) ≤ rhoBar 12570 BstLean.Part154.csC ∧
    rhoBar 12570 BstLean.Part154.csC ≤ 0.000254532015 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035995548558 : ℝ) / (1.295212 * 12570) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035995548559 : ℝ) / (1.29521 * 12570) := by gcongr
      _ ≤ (0.000254532015 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12570 BstLean.Part154.csC) ≤ 0.001018192847 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12570 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) ≤ 0.000194413365 ∧
    cc1 (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) ≤ 0.000123706496 ∧
    cc2 (rhoBar 12570 BstLean.Part154.csC) ≤ 0.000071812545 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12570 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12570 BstLean.Part154.csC * nuR (rhoBar 12570 BstLean.Part154.csC)) ≤ 0.000509080227 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254532015 : ℝ) * 0.001018192847 := by gcongr
      _ ≤ (0.000509080227 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12570 BstLean.Part154.csC) * nuR (rhoBar 12570 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018192847 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12570 BstLean.Part154.csC) * rhoBar 12570 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254532015 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254532015 / 2 + 0.399 * 0.001018192847 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194413365 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509080227 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123706496 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254532015 / 1.414213562 := by gcongr
      _ ≤ (0.000071812545 : ℝ) := by norm_num

end BstLean.Part269.N12570

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12570
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) ≤ 1.63225E-7 := by
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12570 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12570 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194413365 : ℝ) ^ 2 + 0.000123706496 ^ 2 + 3 * 0.000071812545 ^ 2 +
        2 * 0.797885 * 0.000194413365 * 0.000123706496 + 2 * 0.000194413365 * 0.000071812545 +
        4 * 0.797885 * 0.000123706496 * 0.000071812545 := by gcongr
    _ ≤ (1.63225E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12570 BstLean.Part154.csC Θ ≤ 0.002657436004 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12570 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12570 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035995548559 * 1.63225E-7 / (0.000254531621 : ℝ) := by gcongr
    _ ≤ 0.002657436004 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12570 BstLean.Part154.csC Θ ≤ 0.002949102262 + 0.000671491485 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12570 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035995548559 : ℝ) * ((2 * Θ * 0.000254532015 +
        (6863 / 10000) * 0.000254532015 * 12570 * 0.001018192847) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002949102262 + 0.000671491485 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12570 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12570 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12570 0.011 Θ ∧ gammaRatio 12570 0.011 Θ ≤ 0.000087501525 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12570 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035995548559 : ℝ) * 0.525 / ((1 - 0.011) * 12570) := by gcongr
      _ ≤ (0.000087501525 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12570 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12570 0.011 Θ) :=
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
    badAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12570 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12570 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12570 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12570 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12570 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12570 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12570 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12570 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12570 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12570 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035995548559 : ℝ) * 12570 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003692843002 + 0.003328927489 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12570

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12570
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12570 BstLean.Part154.csC) (piBar (rhoBar 12570 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12570 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12570 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12570 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12570 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12570 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12570 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12570 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12570 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12570 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052757963762 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12570) ≤ 0.010651802243 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12570 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035995548559)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010651802243 + 2 * 0.737676 / 12570) := by gcongr
    _ ≤ (0.052757963762 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12570 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12570

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12570
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497628504 : ℝ) ≤ plow 12570 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12570) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947129934)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395153903) : eMP 12570 0.011 xi bn ≤ 0.001200925568 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12570 : ℝ) * (1 - 0.011))) ≤ 0.000593772712 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395153903 / (12570 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593772712 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593772712 : ℝ) + 3.141593 * 0.052947129934 / (12570 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200925568 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947129934)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395153903) : PiBarMP 12570 12 0.011 xi bn ≤ 0.162091426005 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12570 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037351759035 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.497668137051 : ℝ) ≤ √((12570 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.116011345391 : ℝ) ≤ √(12570 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12570) ≤ 0.124267783839 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037351759035 + 0.052947129934 * 1.772454 / (2 * (111.497668137051 : ℝ))) * (1 + 0.001200925568) +
        8 / (12570 * 112.116011345391) + 0.124267783839 := by gcongr
    _ ≤ (0.162091426005 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947129934)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395153903) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282860397331) :
    parallelOracle 12570 0.011 xi bn cd ≤ 0.163092840156 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12570 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12570 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497628504 : ℝ) ≤ plow 12570 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.116011345391 : ℝ) ≤ √(12570 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282860397331 : ℝ) / (2 * 0.560497628504 * 112.116011345391)) * 0.162091426005 +
        0.282860397331 ^ 2 / (2 * 0.560497628504 * 112.116011345391) := by gcongr
    _ ≤ (0.163092840156 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052947129934) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395153903)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282860397331) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12570 12570 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497628504 : ℝ) ≤ plow 12570 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.116011345391 : ℝ) ≤ √(12570 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12570 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12570 Θ 1.22 ≤ 0.011827931480 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.116011345391 := by gcongr <;> linarith
      _ ≤ (0.011827931480 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12570 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12570 12570 0.011 ≤ 0.008525874723 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12570 12570 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12570 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12570 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12570 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12570 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163092840156 + 0.011827931480 + (0.008525874723 : ℝ) *
        (1 + 2 * (0.282860397331 + 0.011827931480) / (0.560497628504 * 112.116011345391))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12570]

end BstLean.Part269.N12570

/-! The original eight local profiles supply actual 12570 moment certificates. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12570 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052947129934 ∧
    0 ≤ bN 12570 BstLean.Part154.csC (groupTheta g) ∧ bN 12570 BstLean.Part154.csC (groupTheta g) ≤ 0.001395153903 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12570 12570 0.011
      (momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12570 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12570 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12570 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230102433569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12570 0.011
      (momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12570 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12570
/-! The actual computed-centre upper energy formula at 12570. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12570

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12570)
open BstLean.Part268 (cell12570)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085878953310
  | 2 => 0.086829065824
  | 3 => 0.087778427541
  | 4 => 0.088728709490
  | 5 => 0.089681924062
  | 6 => 0.090640474552
  | 7 => 0.091607209151
  | 8 => 0.092585479398
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12570 12570 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12570 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12570

/-! Actual upper energy certificates on all 43 source endpoints at 12570. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12570)
open BstLean.Part268 (cell12570)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12570 (gMinus 12570) (1 - (cell12570 i).lower) ≤ 1 ∧
    energyUpper 12570 (gMinus 12570) (BstLean.Part211.gPlus 12570)
      (finiteEnergy 12570 12570 0.011) (1 - (cell12570 i).lower) ≤
      (cell12570 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨10,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨11,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨12,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨13,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨14,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨15,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨16,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨17,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨18,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨19,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨20,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨21,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨22,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨23,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨24,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨25,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨26,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨27,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨28,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨29,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨30,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨31,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨32,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨33,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨34,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨35,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨36,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨37,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨38,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨39,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨40,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨41,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨42,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨43,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨44,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨45,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨46,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨47,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨48,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨49,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨50,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨51,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12570) (by norm_num)
        (q := 1 - (cell12570 ⟨52,by decide⟩).lower)
        (by norm_num [cell12570]) (by norm_num [cell12570])
      exact ⟨E.1,E.2.trans (by norm_num [cell12570])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12570

/-! Source-cell containment and simple scalar guards at 12570. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12570)
open BstLean.Part268 (cell12570)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12570 ⟨10,by decide⟩).lower ∧ (cell12570 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12570 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12570 ⟨11,by decide⟩).lower ∧ (cell12570 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12570 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12570 ⟨12,by decide⟩).lower ∧ (cell12570 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12570 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12570 ⟨13,by decide⟩).lower ∧ (cell12570 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12570 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12570 ⟨14,by decide⟩).lower ∧ (cell12570 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12570 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12570 ⟨15,by decide⟩).lower ∧ (cell12570 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12570 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12570 ⟨16,by decide⟩).lower ∧ (cell12570 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12570 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12570 ⟨17,by decide⟩).lower ∧ (cell12570 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12570 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12570 ⟨18,by decide⟩).lower ∧ (cell12570 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12570 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12570 ⟨19,by decide⟩).lower ∧ (cell12570 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12570 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12570 ⟨20,by decide⟩).lower ∧ (cell12570 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12570 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12570 ⟨21,by decide⟩).lower ∧ (cell12570 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12570 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12570 ⟨22,by decide⟩).lower ∧ (cell12570 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12570 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12570 ⟨23,by decide⟩).lower ∧ (cell12570 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12570 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12570 ⟨24,by decide⟩).lower ∧ (cell12570 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12570 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12570 ⟨25,by decide⟩).lower ∧ (cell12570 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12570 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12570 ⟨26,by decide⟩).lower ∧ (cell12570 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12570 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12570 ⟨27,by decide⟩).lower ∧ (cell12570 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12570 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12570 ⟨28,by decide⟩).lower ∧ (cell12570 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12570 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12570 ⟨29,by decide⟩).lower ∧ (cell12570 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12570 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12570 ⟨30,by decide⟩).lower ∧ (cell12570 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12570 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12570 ⟨31,by decide⟩).lower ∧ (cell12570 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12570 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12570 ⟨32,by decide⟩).lower ∧ (cell12570 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12570 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12570 ⟨33,by decide⟩).lower ∧ (cell12570 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12570 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12570 ⟨34,by decide⟩).lower ∧ (cell12570 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12570 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12570 ⟨35,by decide⟩).lower ∧ (cell12570 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12570 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12570 ⟨36,by decide⟩).lower ∧ (cell12570 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12570 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12570 ⟨37,by decide⟩).lower ∧ (cell12570 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12570 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12570 ⟨38,by decide⟩).lower ∧ (cell12570 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12570 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12570 ⟨39,by decide⟩).lower ∧ (cell12570 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12570 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12570 ⟨40,by decide⟩).lower ∧ (cell12570 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12570 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12570 ⟨41,by decide⟩).lower ∧ (cell12570 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12570 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12570 ⟨42,by decide⟩).lower ∧ (cell12570 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12570 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12570 ⟨43,by decide⟩).lower ∧ (cell12570 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12570 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12570 ⟨44,by decide⟩).lower ∧ (cell12570 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12570 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12570 ⟨45,by decide⟩).lower ∧ (cell12570 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12570 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12570 ⟨46,by decide⟩).lower ∧ (cell12570 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12570 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12570 ⟨47,by decide⟩).lower ∧ (cell12570 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12570 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12570 ⟨48,by decide⟩).lower ∧ (cell12570 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12570 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12570 ⟨49,by decide⟩).lower ∧ (cell12570 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12570 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12570 ⟨50,by decide⟩).lower ∧ (cell12570 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12570 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12570 ⟨51,by decide⟩).lower ∧ (cell12570 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12570 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12570 ⟨52,by decide⟩).lower ∧ (cell12570 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12570 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12570 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12570 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12570,cell12570,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12570 i).lower ∧
    (cell12570 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12570 i).upper ≤ (0.532 : ℝ) ∧
    (cell12570 i).centre ≤ (0.1 : ℝ) ∧ (cell12570 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12570 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12570 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12570

/-! The local source numeric instances at 12570 have no network premises. -/
namespace BstLean.Part269.N12570
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12570)
open BstLean.Part268 (cell12570)

noncomputable def sourceNumerics12570 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12570 (cell12570 i)
      scalarRow12570.M scalarRow12570.H scalarRow12570.xi := by
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
    energy_allowance := scalarRow12570.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12570]
    centre_nonneg := (scalarRow12570.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12570])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12570
/-! Actual 12571 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12571 ≤ (1.035994104184 : ℝ) := by
  have hr : (112.120470923021 : ℝ) ≤ √(12571 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.120470923021 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12571 12571 (11 / 1000) ≤
    (0.008525535604 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12571) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.120470923021 : ℝ) ≤ √(12571 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12571)
  have hdiv : K / √(12571 : ℝ) ≤ K / 112.120470923021 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.120470923021 ≤ (0.008525535604 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12571.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12571 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12571 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12571 := gPlus_lower 12571
end BstLean.Part269.N12571

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12571
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035994104183 : ℝ) ≤ wn 12571 := by
  have hn : √(12571 : ℝ) ≤ 112.120470923022 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12571 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.120470923022 ≤ 2 / √(12571 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254511018 : ℝ) ≤ rhoBar 12571 BstLean.Part154.csC ∧
    rhoBar 12571 BstLean.Part154.csC ≤ 0.000254511412 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035994104183 : ℝ) / (1.295212 * 12571) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035994104184 : ℝ) / (1.29521 * 12571) := by gcongr
      _ ≤ (0.000254511412 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12571 BstLean.Part154.csC) ≤ 0.001018110425 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12571 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) ≤ 0.000194397628 ∧
    cc1 (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) ≤ 0.000123696482 ∧
    cc2 (rhoBar 12571 BstLean.Part154.csC) ≤ 0.000071806732 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12571 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12571 BstLean.Part154.csC * nuR (rhoBar 12571 BstLean.Part154.csC)) ≤ 0.000509039018 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254511412 : ℝ) * 0.001018110425 := by gcongr
      _ ≤ (0.000509039018 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12571 BstLean.Part154.csC) * nuR (rhoBar 12571 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018110425 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12571 BstLean.Part154.csC) * rhoBar 12571 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254511412 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254511412 / 2 + 0.399 * 0.001018110425 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194397628 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509039018 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123696482 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254511412 / 1.414213562 := by gcongr
      _ ≤ (0.000071806732 : ℝ) := by norm_num

end BstLean.Part269.N12571

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12571
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) ≤ 1.63199E-7 := by
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12571 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12571 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194397628 : ℝ) ^ 2 + 0.000123696482 ^ 2 + 3 * 0.000071806732 ^ 2 +
        2 * 0.797885 * 0.000194397628 * 0.000123696482 + 2 * 0.000194397628 * 0.000071806732 +
        4 * 0.797885 * 0.000123696482 * 0.000071806732 := by gcongr
    _ ≤ (1.63199E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12571 BstLean.Part154.csC Θ ≤ 0.002657224087 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12571 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12571 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035994104184 * 1.63199E-7 / (0.000254511018 : ℝ) := by gcongr
    _ ≤ 0.002657224087 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12571 BstLean.Part154.csC Θ ≤ 0.002948855305 + 0.000671436195 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12571 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035994104184 : ℝ) * ((2 * Θ * 0.000254511412 +
        (6863 / 10000) * 0.000254511412 * 12571 * 0.001018110425) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002948855305 + 0.000671436195 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12571 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12571 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12571 0.011 Θ ∧ gammaRatio 12571 0.011 Θ ≤ 0.000087494442 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12571 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035994104184 : ℝ) * 0.525 / ((1 - 0.011) * 12571) := by gcongr
      _ ≤ (0.000087494442 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12571 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12571 0.011 Θ) :=
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
    badAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12571 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12571 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12571 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12571 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12571 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12571 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12571 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12571 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12571 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12571 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035994104184 : ℝ) * 12571 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003692596045 + 0.003328660282 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12571

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12571
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12571 BstLean.Part154.csC) (piBar (rhoBar 12571 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12571 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12571 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12571 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12571 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12571 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12571 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12571 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12571 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12571 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052755842451 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12571) ≤ 0.010651378569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12571 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035994104184)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010651378569 + 2 * 0.737676 / 12571) := by gcongr
    _ ≤ (0.052755842451 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12571 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12571

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12571
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497674663 : ℝ) ≤ plow 12571 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12571) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946742694)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395042646) : eMP 12571 0.011 xi bn ≤ 0.001200829822 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12571 : ℝ) * (1 - 0.011))) ≤ 0.000593725420 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001395042646 / (12571 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593725420 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593725420 : ℝ) + 3.141593 * 0.052946742694 / (12571 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200829822 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946742694)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395042646) : PiBarMP 12571 12 0.011 xi bn ≤ 0.162084968004 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12571 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037350269692 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.502103119178 : ℝ) ≤ √((12571 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.120470923021 : ℝ) ≤ √(12571 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12571) ≤ 0.124262841104 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037350269692 + 0.052946742694 * 1.772454 / (2 * (111.502103119178 : ℝ))) * (1 + 0.001200829822) +
        8 / (12571 * 112.120470923021) + 0.124262841104 := by gcongr
    _ ≤ (0.162084968004 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946742694)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395042646) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282857434567) :
    parallelOracle 12571 0.011 xi bn cd ≤ 0.163086310551 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12571 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12571 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497674663 : ℝ) ≤ plow 12571 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.120470923021 : ℝ) ≤ √(12571 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282857434567 : ℝ) / (2 * 0.560497674663 * 112.120470923021)) * 0.162084968004 +
        0.282857434567 ^ 2 / (2 * 0.560497674663 * 112.120470923021) := by gcongr
    _ ≤ (0.163086310551 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946742694) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001395042646)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282857434567) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12571 12571 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497674663 : ℝ) ≤ plow 12571 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.120470923021 : ℝ) ≤ √(12571 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12571 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12571 Θ 1.22 ≤ 0.011827461026 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.120470923021 := by gcongr <;> linarith
      _ ≤ (0.011827461026 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12571 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12571 12571 0.011 ≤ 0.008525535604 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12571 12571 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12571 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12571 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12571 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12571 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163086310551 + 0.011827461026 + (0.008525535604 : ℝ) *
        (1 + 2 * (0.282857434567 + 0.011827461026) / (0.560497674663 * 112.120470923021))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12571]

end BstLean.Part269.N12571

/-! The original eight local profiles supply actual 12571 moment certificates. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12571 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052946742694 ∧
    0 ≤ bN 12571 BstLean.Part154.csC (groupTheta g) ∧ bN 12571 BstLean.Part154.csC (groupTheta g) ≤ 0.001395042646 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12571 12571 0.011
      (momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12571 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12571 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12571 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230101592116 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12571 0.011
      (momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12571 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12571
/-! The actual computed-centre upper energy formula at 12571. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12571

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12571)
open BstLean.Part268 (cell12571)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085875886903
  | 2 => 0.086825939563
  | 3 => 0.087775232137
  | 4 => 0.088725433558
  | 5 => 0.089678553754
  | 6 => 0.090636993155
  | 7 => 0.091603596633
  | 8 => 0.092581711906
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12571 12571 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12571 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12571

/-! Actual upper energy certificates on all 43 source endpoints at 12571. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12571)
open BstLean.Part268 (cell12571)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12571 (gMinus 12571) (1 - (cell12571 i).lower) ≤ 1 ∧
    energyUpper 12571 (gMinus 12571) (BstLean.Part211.gPlus 12571)
      (finiteEnergy 12571 12571 0.011) (1 - (cell12571 i).lower) ≤
      (cell12571 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨10,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨11,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨12,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨13,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨14,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨15,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨16,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨17,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨18,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨19,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨20,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨21,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨22,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨23,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨24,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨25,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨26,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨27,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨28,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨29,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨30,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨31,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨32,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨33,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨34,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨35,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨36,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨37,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨38,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨39,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨40,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨41,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨42,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨43,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨44,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨45,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨46,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨47,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨48,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨49,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨50,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨51,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12571) (by norm_num)
        (q := 1 - (cell12571 ⟨52,by decide⟩).lower)
        (by norm_num [cell12571]) (by norm_num [cell12571])
      exact ⟨E.1,E.2.trans (by norm_num [cell12571])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12571

/-! Source-cell containment and simple scalar guards at 12571. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12571)
open BstLean.Part268 (cell12571)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12571 ⟨10,by decide⟩).lower ∧ (cell12571 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12571 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12571 ⟨11,by decide⟩).lower ∧ (cell12571 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12571 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12571 ⟨12,by decide⟩).lower ∧ (cell12571 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12571 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12571 ⟨13,by decide⟩).lower ∧ (cell12571 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12571 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12571 ⟨14,by decide⟩).lower ∧ (cell12571 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12571 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12571 ⟨15,by decide⟩).lower ∧ (cell12571 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12571 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12571 ⟨16,by decide⟩).lower ∧ (cell12571 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12571 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12571 ⟨17,by decide⟩).lower ∧ (cell12571 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12571 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12571 ⟨18,by decide⟩).lower ∧ (cell12571 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12571 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12571 ⟨19,by decide⟩).lower ∧ (cell12571 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12571 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12571 ⟨20,by decide⟩).lower ∧ (cell12571 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12571 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12571 ⟨21,by decide⟩).lower ∧ (cell12571 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12571 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12571 ⟨22,by decide⟩).lower ∧ (cell12571 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12571 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12571 ⟨23,by decide⟩).lower ∧ (cell12571 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12571 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12571 ⟨24,by decide⟩).lower ∧ (cell12571 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12571 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12571 ⟨25,by decide⟩).lower ∧ (cell12571 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12571 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12571 ⟨26,by decide⟩).lower ∧ (cell12571 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12571 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12571 ⟨27,by decide⟩).lower ∧ (cell12571 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12571 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12571 ⟨28,by decide⟩).lower ∧ (cell12571 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12571 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12571 ⟨29,by decide⟩).lower ∧ (cell12571 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12571 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12571 ⟨30,by decide⟩).lower ∧ (cell12571 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12571 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12571 ⟨31,by decide⟩).lower ∧ (cell12571 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12571 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12571 ⟨32,by decide⟩).lower ∧ (cell12571 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12571 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12571 ⟨33,by decide⟩).lower ∧ (cell12571 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12571 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12571 ⟨34,by decide⟩).lower ∧ (cell12571 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12571 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12571 ⟨35,by decide⟩).lower ∧ (cell12571 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12571 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12571 ⟨36,by decide⟩).lower ∧ (cell12571 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12571 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12571 ⟨37,by decide⟩).lower ∧ (cell12571 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12571 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12571 ⟨38,by decide⟩).lower ∧ (cell12571 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12571 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12571 ⟨39,by decide⟩).lower ∧ (cell12571 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12571 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12571 ⟨40,by decide⟩).lower ∧ (cell12571 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12571 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12571 ⟨41,by decide⟩).lower ∧ (cell12571 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12571 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12571 ⟨42,by decide⟩).lower ∧ (cell12571 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12571 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12571 ⟨43,by decide⟩).lower ∧ (cell12571 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12571 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12571 ⟨44,by decide⟩).lower ∧ (cell12571 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12571 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12571 ⟨45,by decide⟩).lower ∧ (cell12571 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12571 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12571 ⟨46,by decide⟩).lower ∧ (cell12571 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12571 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12571 ⟨47,by decide⟩).lower ∧ (cell12571 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12571 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12571 ⟨48,by decide⟩).lower ∧ (cell12571 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12571 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12571 ⟨49,by decide⟩).lower ∧ (cell12571 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12571 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12571 ⟨50,by decide⟩).lower ∧ (cell12571 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12571 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12571 ⟨51,by decide⟩).lower ∧ (cell12571 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12571 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12571 ⟨52,by decide⟩).lower ∧ (cell12571 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12571 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12571 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12571 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12571,cell12571,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12571 i).lower ∧
    (cell12571 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12571 i).upper ≤ (0.532 : ℝ) ∧
    (cell12571 i).centre ≤ (0.1 : ℝ) ∧ (cell12571 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12571 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12571 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12571

/-! The local source numeric instances at 12571 have no network premises. -/
namespace BstLean.Part269.N12571
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12571)
open BstLean.Part268 (cell12571)

noncomputable def sourceNumerics12571 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12571 (cell12571 i)
      scalarRow12571.M scalarRow12571.H scalarRow12571.xi := by
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
    energy_allowance := scalarRow12571.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12571]
    centre_nonneg := (scalarRow12571.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12571])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12571
/-! Actual 12572 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12572 ≤ (1.035992659982 : ℝ) := by
  have hr : (112.124930323278 : ℝ) ≤ √(12572 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.124930323278 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12572 12572 (11 / 1000) ≤
    (0.008525196527 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12572) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.124930323278 : ℝ) ≤ √(12572 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12572)
  have hdiv : K / √(12572 : ℝ) ≤ K / 112.124930323278 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.124930323278 ≤ (0.008525196527 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12572.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12572 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12572 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12572 := gPlus_lower 12572
end BstLean.Part269.N12572

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12572
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035992659981 : ℝ) ≤ wn 12572 := by
  have hn : √(12572 : ℝ) ≤ 112.124930323279 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12572 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.124930323279 ≤ 2 / √(12572 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254490419 : ℝ) ≤ rhoBar 12572 BstLean.Part154.csC ∧
    rhoBar 12572 BstLean.Part154.csC ≤ 0.000254490813 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035992659981 : ℝ) / (1.295212 * 12572) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035992659982 : ℝ) / (1.29521 * 12572) := by gcongr
      _ ≤ (0.000254490813 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12572 BstLean.Part154.csC) ≤ 0.001018028018 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12572 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) ≤ 0.000194381893 ∧
    cc1 (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) ≤ 0.000123686470 ∧
    cc2 (rhoBar 12572 BstLean.Part154.csC) ≤ 0.000071800920 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12572 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12572 BstLean.Part154.csC * nuR (rhoBar 12572 BstLean.Part154.csC)) ≤ 0.000508997818 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254490813 : ℝ) * 0.001018028018 := by gcongr
      _ ≤ (0.000508997818 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12572 BstLean.Part154.csC) * nuR (rhoBar 12572 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018028018 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12572 BstLean.Part154.csC) * rhoBar 12572 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254490813 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254490813 / 2 + 0.399 * 0.001018028018 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194381893 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508997818 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123686470 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254490813 / 1.414213562 := by gcongr
      _ ≤ (0.000071800920 : ℝ) := by norm_num

end BstLean.Part269.N12572

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12572
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) ≤ 1.63172E-7 := by
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12572 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12572 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194381893 : ℝ) ^ 2 + 0.000123686470 ^ 2 + 3 * 0.000071800920 ^ 2 +
        2 * 0.797885 * 0.000194381893 * 0.000123686470 + 2 * 0.000194381893 * 0.000071800920 +
        4 * 0.797885 * 0.000123686470 * 0.000071800920 := by gcongr
    _ ≤ (1.63172E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12572 BstLean.Part154.csC Θ ≤ 0.002656995812 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12572 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12572 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035992659982 * 1.63172E-7 / (0.000254490419 : ℝ) := by gcongr
    _ ≤ 0.002656995812 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12572 BstLean.Part154.csC Θ ≤ 0.002948608401 + 0.000671380916 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12572 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035992659982 : ℝ) * ((2 * Θ * 0.000254490813 +
        (6863 / 10000) * 0.000254490813 * 12572 * 0.001018028018) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002948608401 + 0.000671380916 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12572 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12572 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12572 0.011 Θ ∧ gammaRatio 12572 0.011 Θ ≤ 0.000087487361 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12572 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035992659982 : ℝ) * 0.525 / ((1 - 0.011) * 12572) := by gcongr
      _ ≤ (0.000087487361 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12572 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12572 0.011 Θ) :=
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
    badAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12572 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12572 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12572 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12572 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12572 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12572 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12572 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12572 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12572 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12572 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035992659982 : ℝ) * 12572 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003692349141 + 0.003328376728 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12572

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12572
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12572 BstLean.Part154.csC) (piBar (rhoBar 12572 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12572 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12572 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12572 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12572 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12572 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12572 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12572 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12572 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12572 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052753721393 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12572) ≤ 0.010650954945 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12572 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035992659982)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010650954945 + 2 * 0.737676 / 12572) := by gcongr
    _ ≤ (0.052753721393 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12572 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12572

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12572
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497720816 : ℝ) ≤ plow 12572 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12572) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946346924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394922802) : eMP 12572 0.011 xi bn ≤ 0.001200730428 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12572 : ℝ) * (1 - 0.011))) ≤ 0.000593676305 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394922802 / (12572 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593676305 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593676305 : ℝ) + 3.141593 * 0.052946346924 / (12572 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200730428 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946346924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394922802) : PiBarMP 12572 12 0.011 xi bn ≤ 0.162078395233 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12572 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037348665331 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.506537924912 : ℝ) ≤ √((12572 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.124930323278 : ℝ) ≤ √(12572 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12572) ≤ 0.124257898958 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037348665331 + 0.052946346924 * 1.772454 / (2 * (111.506537924912 : ℝ))) * (1 + 0.001200730428) +
        8 / (12572 * 112.124930323278) + 0.124257898958 := by gcongr
    _ ≤ (0.162078395233 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946346924)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394922802) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282854453517) :
    parallelOracle 12572 0.011 xi bn cd ≤ 0.163079665820 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12572 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12572 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497720816 : ℝ) ≤ plow 12572 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.124930323278 : ℝ) ≤ √(12572 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282854453517 : ℝ) / (2 * 0.560497720816 * 112.124930323278)) * 0.162078395233 +
        0.282854453517 ^ 2 / (2 * 0.560497720816 * 112.124930323278) := by gcongr
    _ ≤ (0.163079665820 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052946346924) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394922802)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282854453517) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12572 12572 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497720816 : ℝ) ≤ plow 12572 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.124930323278 : ℝ) ≤ √(12572 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12572 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12572 Θ 1.22 ≤ 0.011826990628 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.124930323278 := by gcongr <;> linarith
      _ ≤ (0.011826990628 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12572 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12572 12572 0.011 ≤ 0.008525196527 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12572 12572 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12572 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12572 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12572 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12572 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163079665820 + 0.011826990628 + (0.008525196527 : ℝ) *
        (1 + 2 * (0.282854453517 + 0.011826990628) / (0.560497720816 * 112.124930323278))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12572]

end BstLean.Part269.N12572

/-! The original eight local profiles supply actual 12572 moment certificates. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12572 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052946346924 ∧
    0 ≤ bN 12572 BstLean.Part154.csC (groupTheta g) ∧ bN 12572 BstLean.Part154.csC (groupTheta g) ≤ 0.001394922802 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12572 12572 0.011
      (momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12572 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12572 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12572 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230100732124 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12572 0.011
      (momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12572 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12572
/-! The actual computed-centre upper energy formula at 12572. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12572

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12572)
open BstLean.Part268 (cell12572)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085872821733
  | 2 => 0.086822814593
  | 3 => 0.087772038090
  | 4 => 0.088722159061
  | 5 => 0.089675184980
  | 6 => 0.090633513410
  | 7 => 0.091599985908
  | 8 => 0.092577946379
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12572 12572 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12572 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12572

/-! Actual upper energy certificates on all 43 source endpoints at 12572. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12572)
open BstLean.Part268 (cell12572)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12572 (gMinus 12572) (1 - (cell12572 i).lower) ≤ 1 ∧
    energyUpper 12572 (gMinus 12572) (BstLean.Part211.gPlus 12572)
      (finiteEnergy 12572 12572 0.011) (1 - (cell12572 i).lower) ≤
      (cell12572 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨10,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨11,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨12,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨13,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨14,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨15,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨16,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨17,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨18,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨19,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨20,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨21,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨22,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨23,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨24,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨25,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨26,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨27,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨28,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨29,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨30,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨31,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨32,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨33,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨34,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨35,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨36,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨37,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨38,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨39,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨40,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨41,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨42,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨43,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨44,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨45,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨46,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨47,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨48,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨49,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨50,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨51,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12572) (by norm_num)
        (q := 1 - (cell12572 ⟨52,by decide⟩).lower)
        (by norm_num [cell12572]) (by norm_num [cell12572])
      exact ⟨E.1,E.2.trans (by norm_num [cell12572])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12572

/-! Source-cell containment and simple scalar guards at 12572. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12572)
open BstLean.Part268 (cell12572)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12572 ⟨10,by decide⟩).lower ∧ (cell12572 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12572 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12572 ⟨11,by decide⟩).lower ∧ (cell12572 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12572 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12572 ⟨12,by decide⟩).lower ∧ (cell12572 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12572 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12572 ⟨13,by decide⟩).lower ∧ (cell12572 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12572 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12572 ⟨14,by decide⟩).lower ∧ (cell12572 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12572 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12572 ⟨15,by decide⟩).lower ∧ (cell12572 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12572 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12572 ⟨16,by decide⟩).lower ∧ (cell12572 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12572 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12572 ⟨17,by decide⟩).lower ∧ (cell12572 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12572 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12572 ⟨18,by decide⟩).lower ∧ (cell12572 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12572 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12572 ⟨19,by decide⟩).lower ∧ (cell12572 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12572 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12572 ⟨20,by decide⟩).lower ∧ (cell12572 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12572 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12572 ⟨21,by decide⟩).lower ∧ (cell12572 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12572 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12572 ⟨22,by decide⟩).lower ∧ (cell12572 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12572 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12572 ⟨23,by decide⟩).lower ∧ (cell12572 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12572 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12572 ⟨24,by decide⟩).lower ∧ (cell12572 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12572 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12572 ⟨25,by decide⟩).lower ∧ (cell12572 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12572 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12572 ⟨26,by decide⟩).lower ∧ (cell12572 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12572 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12572 ⟨27,by decide⟩).lower ∧ (cell12572 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12572 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12572 ⟨28,by decide⟩).lower ∧ (cell12572 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12572 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12572 ⟨29,by decide⟩).lower ∧ (cell12572 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12572 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12572 ⟨30,by decide⟩).lower ∧ (cell12572 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12572 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12572 ⟨31,by decide⟩).lower ∧ (cell12572 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12572 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12572 ⟨32,by decide⟩).lower ∧ (cell12572 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12572 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12572 ⟨33,by decide⟩).lower ∧ (cell12572 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12572 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12572 ⟨34,by decide⟩).lower ∧ (cell12572 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12572 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12572 ⟨35,by decide⟩).lower ∧ (cell12572 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12572 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12572 ⟨36,by decide⟩).lower ∧ (cell12572 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12572 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12572 ⟨37,by decide⟩).lower ∧ (cell12572 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12572 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12572 ⟨38,by decide⟩).lower ∧ (cell12572 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12572 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12572 ⟨39,by decide⟩).lower ∧ (cell12572 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12572 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12572 ⟨40,by decide⟩).lower ∧ (cell12572 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12572 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12572 ⟨41,by decide⟩).lower ∧ (cell12572 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12572 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12572 ⟨42,by decide⟩).lower ∧ (cell12572 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12572 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12572 ⟨43,by decide⟩).lower ∧ (cell12572 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12572 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12572 ⟨44,by decide⟩).lower ∧ (cell12572 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12572 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12572 ⟨45,by decide⟩).lower ∧ (cell12572 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12572 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12572 ⟨46,by decide⟩).lower ∧ (cell12572 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12572 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12572 ⟨47,by decide⟩).lower ∧ (cell12572 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12572 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12572 ⟨48,by decide⟩).lower ∧ (cell12572 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12572 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12572 ⟨49,by decide⟩).lower ∧ (cell12572 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12572 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12572 ⟨50,by decide⟩).lower ∧ (cell12572 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12572 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12572 ⟨51,by decide⟩).lower ∧ (cell12572 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12572 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12572 ⟨52,by decide⟩).lower ∧ (cell12572 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12572 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12572 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12572 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12572,cell12572,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12572 i).lower ∧
    (cell12572 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12572 i).upper ≤ (0.532 : ℝ) ∧
    (cell12572 i).centre ≤ (0.1 : ℝ) ∧ (cell12572 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12572 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12572 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12572

/-! The local source numeric instances at 12572 have no network premises. -/
namespace BstLean.Part269.N12572
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12572)
open BstLean.Part268 (cell12572)

noncomputable def sourceNumerics12572 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12572 (cell12572 i)
      scalarRow12572.M scalarRow12572.H scalarRow12572.xi := by
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
    energy_allowance := scalarRow12572.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12572]
    centre_nonneg := (scalarRow12572.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12572])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12572
/-! Actual 12573 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12573 ≤ (1.035991215954 : ℝ) := by
  have hr : (112.129389546184 : ℝ) ≤ √(12573 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.129389546184 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12573 12573 (11 / 1000) ≤
    (0.008524857489 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12573) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.129389546184 : ℝ) ≤ √(12573 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12573)
  have hdiv : K / √(12573 : ℝ) ≤ K / 112.129389546184 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.129389546184 ≤ (0.008524857489 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12573.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12573 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12573 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12573 := gPlus_lower 12573
end BstLean.Part269.N12573

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12573
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035991215953 : ℝ) ≤ wn 12573 := by
  have hn : √(12573 : ℝ) ≤ 112.129389546185 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12573 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.129389546185 ≤ 2 / √(12573 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254469823 : ℝ) ≤ rhoBar 12573 BstLean.Part154.csC ∧
    rhoBar 12573 BstLean.Part154.csC ≤ 0.000254470217 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035991215953 : ℝ) / (1.295212 * 12573) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035991215954 : ℝ) / (1.29521 * 12573) := by gcongr
      _ ≤ (0.000254470217 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12573 BstLean.Part154.csC) ≤ 0.001017945624 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12573 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) ≤ 0.000194366161 ∧
    cc1 (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) ≤ 0.000123676460 ∧
    cc2 (rhoBar 12573 BstLean.Part154.csC) ≤ 0.000071795109 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12573 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12573 BstLean.Part154.csC * nuR (rhoBar 12573 BstLean.Part154.csC)) ≤ 0.000508956623 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254470217 : ℝ) * 0.001017945624 := by gcongr
      _ ≤ (0.000508956623 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12573 BstLean.Part154.csC) * nuR (rhoBar 12573 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017945624 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12573 BstLean.Part154.csC) * rhoBar 12573 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254470217 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254470217 / 2 + 0.399 * 0.001017945624 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194366161 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508956623 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123676460 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254470217 / 1.414213562 := by gcongr
      _ ≤ (0.000071795109 : ℝ) := by norm_num

end BstLean.Part269.N12573

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12573
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) ≤ 1.63146E-7 := by
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12573 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12573 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194366161 : ℝ) ^ 2 + 0.000123676460 ^ 2 + 3 * 0.000071795109 ^ 2 +
        2 * 0.797885 * 0.000194366161 * 0.000123676460 + 2 * 0.000194366161 * 0.000071795109 +
        4 * 0.797885 * 0.000123676460 * 0.000071795109 := by gcongr
    _ ≤ (1.63146E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12573 BstLean.Part154.csC Θ ≤ 0.002656783755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12573 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12573 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035991215954 * 1.63146E-7 / (0.000254469823 : ℝ) := by gcongr
    _ ≤ 0.002656783755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12573 BstLean.Part154.csC Θ ≤ 0.002948361534 + 0.000671325646 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12573 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035991215954 : ℝ) * ((2 * Θ * 0.000254470217 +
        (6863 / 10000) * 0.000254470217 * 12573 * 0.001017945624) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002948361534 + 0.000671325646 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12573 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12573 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12573 0.011 Θ ∧ gammaRatio 12573 0.011 Θ ≤ 0.000087480281 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12573 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035991215954 : ℝ) * 0.525 / ((1 - 0.011) * 12573) := by gcongr
      _ ≤ (0.000087480281 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12573 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12573 0.011 Θ) :=
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
    badAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12573 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12573 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12573 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12573 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12573 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12573 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12573 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12573 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12573 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12573 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035991215954 : ℝ) * 12573 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003692102274 + 0.003328109401 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12573

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12573
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12573 BstLean.Part154.csC) (piBar (rhoBar 12573 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12573 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12573 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12573 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12573 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12573 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12573 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12573 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12573 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12573 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052751600592 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12573) ≤ 0.010650531372 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12573 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035991215954)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010650531372 + 2 * 0.737676 / 12573) := by gcongr
    _ ≤ (0.052751600592 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12573 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12573

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12573
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497766960 : ℝ) ≤ plow 12573 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12573) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945959710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394811472) : eMP 12573 0.011 xi bn ≤ 0.001200634666 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12573 : ℝ) * (1 - 0.011))) ≤ 0.000593629005 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394811472 / (12573 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593629005 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593629005 : ℝ) + 3.141593 * 0.052945959710 / (12573 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200634666 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945959710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394811472) : PiBarMP 12573 12 0.011 xi bn ≤ 0.162071937314 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12573 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037347174887 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.510972554273 : ℝ) ≤ √((12573 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.129389546184 : ℝ) ≤ √(12573 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12573) ≤ 0.124252957402 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037347174887 + 0.052945959710 * 1.772454 / (2 * (111.510972554273 : ℝ))) * (1 + 0.001200634666) +
        8 / (12573 * 112.129389546184) + 0.124252957402 := by gcongr
    _ ≤ (0.162071937314 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945959710)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394811472) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282851491314) :
    parallelOracle 12573 0.011 xi bn cd ≤ 0.163073136316 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12573 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12573 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497766960 : ℝ) ≤ plow 12573 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.129389546184 : ℝ) ≤ √(12573 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282851491314 : ℝ) / (2 * 0.560497766960 * 112.129389546184)) * 0.162071937314 +
        0.282851491314 ^ 2 / (2 * 0.560497766960 * 112.129389546184) := by gcongr
    _ ≤ (0.163073136316 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945959710) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394811472)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282851491314) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12573 12573 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497766960 : ℝ) ≤ plow 12573 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.129389546184 : ℝ) ≤ √(12573 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12573 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12573 Θ 1.22 ≤ 0.011826520285 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.129389546184 := by gcongr <;> linarith
      _ ≤ (0.011826520285 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12573 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12573 12573 0.011 ≤ 0.008524857489 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12573 12573 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12573 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12573 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12573 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12573 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163073136316 + 0.011826520285 + (0.008524857489 : ℝ) *
        (1 + 2 * (0.282851491314 + 0.011826520285) / (0.560497766960 * 112.129389546184))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12573]

end BstLean.Part269.N12573

/-! The original eight local profiles supply actual 12573 moment certificates. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12573 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052945959710 ∧
    0 ≤ bN 12573 BstLean.Part154.csC (groupTheta g) ∧ bN 12573 BstLean.Part154.csC (groupTheta g) ≤ 0.001394811472 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12573 12573 0.011
      (momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12573 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12573 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12573 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230099890722 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12573 0.011
      (momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12573 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12573
/-! The actual computed-centre upper energy formula at 12573. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12573

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12573)
open BstLean.Part268 (cell12573)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085869757801
  | 2 => 0.086819690912
  | 3 => 0.087768845396
  | 4 => 0.088718885998
  | 5 => 0.089671817736
  | 6 => 0.090630035313
  | 7 => 0.091596376976
  | 8 => 0.092574182815
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12573 12573 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12573 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12573

/-! Actual upper energy certificates on all 43 source endpoints at 12573. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12573)
open BstLean.Part268 (cell12573)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12573 (gMinus 12573) (1 - (cell12573 i).lower) ≤ 1 ∧
    energyUpper 12573 (gMinus 12573) (BstLean.Part211.gPlus 12573)
      (finiteEnergy 12573 12573 0.011) (1 - (cell12573 i).lower) ≤
      (cell12573 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨10,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨11,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨12,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨13,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨14,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨15,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨16,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨17,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨18,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨19,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨20,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨21,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨22,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨23,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨24,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨25,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨26,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨27,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨28,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨29,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨30,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨31,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨32,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨33,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨34,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨35,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨36,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨37,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨38,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨39,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨40,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨41,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨42,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨43,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨44,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨45,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨46,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨47,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨48,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨49,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨50,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨51,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12573) (by norm_num)
        (q := 1 - (cell12573 ⟨52,by decide⟩).lower)
        (by norm_num [cell12573]) (by norm_num [cell12573])
      exact ⟨E.1,E.2.trans (by norm_num [cell12573])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12573

/-! Source-cell containment and simple scalar guards at 12573. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12573)
open BstLean.Part268 (cell12573)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12573 ⟨10,by decide⟩).lower ∧ (cell12573 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12573 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12573 ⟨11,by decide⟩).lower ∧ (cell12573 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12573 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12573 ⟨12,by decide⟩).lower ∧ (cell12573 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12573 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12573 ⟨13,by decide⟩).lower ∧ (cell12573 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12573 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12573 ⟨14,by decide⟩).lower ∧ (cell12573 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12573 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12573 ⟨15,by decide⟩).lower ∧ (cell12573 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12573 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12573 ⟨16,by decide⟩).lower ∧ (cell12573 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12573 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12573 ⟨17,by decide⟩).lower ∧ (cell12573 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12573 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12573 ⟨18,by decide⟩).lower ∧ (cell12573 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12573 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12573 ⟨19,by decide⟩).lower ∧ (cell12573 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12573 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12573 ⟨20,by decide⟩).lower ∧ (cell12573 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12573 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12573 ⟨21,by decide⟩).lower ∧ (cell12573 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12573 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12573 ⟨22,by decide⟩).lower ∧ (cell12573 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12573 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12573 ⟨23,by decide⟩).lower ∧ (cell12573 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12573 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12573 ⟨24,by decide⟩).lower ∧ (cell12573 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12573 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12573 ⟨25,by decide⟩).lower ∧ (cell12573 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12573 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12573 ⟨26,by decide⟩).lower ∧ (cell12573 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12573 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12573 ⟨27,by decide⟩).lower ∧ (cell12573 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12573 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12573 ⟨28,by decide⟩).lower ∧ (cell12573 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12573 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12573 ⟨29,by decide⟩).lower ∧ (cell12573 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12573 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12573 ⟨30,by decide⟩).lower ∧ (cell12573 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12573 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12573 ⟨31,by decide⟩).lower ∧ (cell12573 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12573 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12573 ⟨32,by decide⟩).lower ∧ (cell12573 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12573 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12573 ⟨33,by decide⟩).lower ∧ (cell12573 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12573 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12573 ⟨34,by decide⟩).lower ∧ (cell12573 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12573 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12573 ⟨35,by decide⟩).lower ∧ (cell12573 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12573 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12573 ⟨36,by decide⟩).lower ∧ (cell12573 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12573 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12573 ⟨37,by decide⟩).lower ∧ (cell12573 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12573 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12573 ⟨38,by decide⟩).lower ∧ (cell12573 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12573 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12573 ⟨39,by decide⟩).lower ∧ (cell12573 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12573 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12573 ⟨40,by decide⟩).lower ∧ (cell12573 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12573 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12573 ⟨41,by decide⟩).lower ∧ (cell12573 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12573 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12573 ⟨42,by decide⟩).lower ∧ (cell12573 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12573 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12573 ⟨43,by decide⟩).lower ∧ (cell12573 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12573 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12573 ⟨44,by decide⟩).lower ∧ (cell12573 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12573 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12573 ⟨45,by decide⟩).lower ∧ (cell12573 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12573 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12573 ⟨46,by decide⟩).lower ∧ (cell12573 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12573 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12573 ⟨47,by decide⟩).lower ∧ (cell12573 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12573 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12573 ⟨48,by decide⟩).lower ∧ (cell12573 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12573 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12573 ⟨49,by decide⟩).lower ∧ (cell12573 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12573 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12573 ⟨50,by decide⟩).lower ∧ (cell12573 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12573 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12573 ⟨51,by decide⟩).lower ∧ (cell12573 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12573 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12573 ⟨52,by decide⟩).lower ∧ (cell12573 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12573 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12573 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12573 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12573,cell12573,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12573 i).lower ∧
    (cell12573 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12573 i).upper ≤ (0.532 : ℝ) ∧
    (cell12573 i).centre ≤ (0.1 : ℝ) ∧ (cell12573 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12573 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12573 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12573

/-! The local source numeric instances at 12573 have no network premises. -/
namespace BstLean.Part269.N12573
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12573)
open BstLean.Part268 (cell12573)

noncomputable def sourceNumerics12573 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12573 (cell12573 i)
      scalarRow12573.M scalarRow12573.H scalarRow12573.xi := by
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
    energy_allowance := scalarRow12573.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12573]
    centre_nonneg := (scalarRow12573.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12573])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12573
/-! Actual 12574 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12574 ≤ (1.035989772099 : ℝ) := by
  have hr : (112.133848591761 : ℝ) ≤ √(12574 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.133848591761 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12574 12574 (11 / 1000) ≤
    (0.008524518492 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12574) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.133848591761 : ℝ) ≤ √(12574 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12574)
  have hdiv : K / √(12574 : ℝ) ≤ K / 112.133848591761 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.133848591761 ≤ (0.008524518492 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12574.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12574 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12574 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12574 := gPlus_lower 12574
end BstLean.Part269.N12574

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12574
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035989772098 : ℝ) ≤ wn 12574 := by
  have hn : √(12574 : ℝ) ≤ 112.133848591762 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12574 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.133848591762 ≤ 2 / √(12574 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254449231 : ℝ) ≤ rhoBar 12574 BstLean.Part154.csC ∧
    rhoBar 12574 BstLean.Part154.csC ≤ 0.000254449625 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035989772098 : ℝ) / (1.295212 * 12574) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035989772099 : ℝ) / (1.29521 * 12574) := by gcongr
      _ ≤ (0.000254449625 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12574 BstLean.Part154.csC) ≤ 0.001017863245 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12574 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) ≤ 0.000194350432 ∧
    cc1 (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) ≤ 0.000123666451 ∧
    cc2 (rhoBar 12574 BstLean.Part154.csC) ≤ 0.000071789300 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12574 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12574 BstLean.Part154.csC * nuR (rhoBar 12574 BstLean.Part154.csC)) ≤ 0.000508915436 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254449625 : ℝ) * 0.001017863245 := by gcongr
      _ ≤ (0.000508915436 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12574 BstLean.Part154.csC) * nuR (rhoBar 12574 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017863245 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12574 BstLean.Part154.csC) * rhoBar 12574 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254449625 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254449625 / 2 + 0.399 * 0.001017863245 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194350432 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508915436 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123666451 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254449625 / 1.414213562 := by gcongr
      _ ≤ (0.000071789300 : ℝ) := by norm_num

end BstLean.Part269.N12574

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12574
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) ≤ 1.63120E-7 := by
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12574 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12574 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194350432 : ℝ) ^ 2 + 0.000123666451 ^ 2 + 3 * 0.000071789300 ^ 2 +
        2 * 0.797885 * 0.000194350432 * 0.000123666451 + 2 * 0.000194350432 * 0.000071789300 +
        4 * 0.797885 * 0.000123666451 * 0.000071789300 := by gcongr
    _ ≤ (1.63120E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12574 BstLean.Part154.csC Θ ≤ 0.002656571623 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12574 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12574 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035989772099 * 1.63120E-7 / (0.000254449231 : ℝ) := by gcongr
    _ ≤ 0.002656571623 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12574 BstLean.Part154.csC Θ ≤ 0.002948114720 + 0.000671270386 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12574 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035989772099 : ℝ) * ((2 * Θ * 0.000254449625 +
        (6863 / 10000) * 0.000254449625 * 12574 * 0.001017863245) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002948114720 + 0.000671270386 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12574 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12574 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12574 0.011 Θ ∧ gammaRatio 12574 0.011 Θ ≤ 0.000087473201 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12574 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035989772099 : ℝ) * 0.525 / ((1 - 0.011) * 12574) := by gcongr
      _ ≤ (0.000087473201 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12574 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12574 0.011 Θ) :=
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
    badAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12574 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12574 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12574 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12574 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12574 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12574 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12574 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12574 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12574 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12574 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035989772099 : ℝ) * 12574 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003691855460 + 0.003327842009 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12574

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12574
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12574 BstLean.Part154.csC) (piBar (rhoBar 12574 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12574 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12574 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12574 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12574 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12574 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12574 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12574 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12574 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12574 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052749480048 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12574) ≤ 0.010650107850 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12574 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035989772099)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010650107850 + 2 * 0.737676 / 12574) := by gcongr
    _ ≤ (0.052749480048 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12574 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12574

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12574
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497813098 : ℝ) ≤ plow 12574 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12574) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945572515)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394700103) : eMP 12574 0.011 xi bn ≤ 0.001200538894 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12574 : ℝ) * (1 - 0.011))) ≤ 0.000593581700 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394700103 / (12574 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593581700 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593581700 : ℝ) + 3.141593 * 0.052945572515 / (12574 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200538894 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945572515)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394700103) : PiBarMP 12574 12 0.011 xi bn ≤ 0.162065479404 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12574 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037345683861 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.515407007283 : ℝ) ≤ √((12574 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.133848591761 : ℝ) ≤ √(12574 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12574) ≤ 0.124248016436 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037345683861 + 0.052945572515 * 1.772454 / (2 * (111.515407007283 : ℝ))) * (1 + 0.001200538894) +
        8 / (12574 * 112.133848591761) + 0.124248016436 := by gcongr
    _ ≤ (0.162065479404 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945572515)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394700103) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282848529406) :
    parallelOracle 12574 0.011 xi bn cd ≤ 0.163066606831 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12574 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12574 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497813098 : ℝ) ≤ plow 12574 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.133848591761 : ℝ) ≤ √(12574 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282848529406 : ℝ) / (2 * 0.560497813098 * 112.133848591761)) * 0.162065479404 +
        0.282848529406 ^ 2 / (2 * 0.560497813098 * 112.133848591761) := by gcongr
    _ ≤ (0.163066606831 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052945572515) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394700103)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282848529406) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12574 12574 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497813098 : ℝ) ≤ plow 12574 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.133848591761 : ℝ) ≤ √(12574 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12574 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12574 Θ 1.22 ≤ 0.011826049999 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.133848591761 := by gcongr <;> linarith
      _ ≤ (0.011826049999 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12574 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12574 12574 0.011 ≤ 0.008524518492 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12574 12574 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12574 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12574 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12574 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12574 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163066606831 + 0.011826049999 + (0.008524518492 : ℝ) *
        (1 + 2 * (0.282848529406 + 0.011826049999) / (0.560497813098 * 112.133848591761))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12574]

end BstLean.Part269.N12574

/-! The original eight local profiles supply actual 12574 moment certificates. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12574 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052945572515 ∧
    0 ≤ bN 12574 BstLean.Part154.csC (groupTheta g) ∧ bN 12574 BstLean.Part154.csC (groupTheta g) ≤ 0.001394700103 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12574 12574 0.011
      (momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12574 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12574 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12574 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230099049358 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12574 0.011
      (momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12574 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12574
/-! The actual computed-centre upper energy formula at 12574. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12574

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12574)
open BstLean.Part268 (cell12574)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085866695104
  | 2 => 0.086816568520
  | 3 => 0.087765654056
  | 4 => 0.088715614367
  | 5 => 0.089668452021
  | 6 => 0.090626558864
  | 7 => 0.091592769833
  | 8 => 0.092570421212
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12574 12574 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12574 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003697790472 + 0.003334422039 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S8.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S8.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12574

/-! Actual upper energy certificates on all 43 source endpoints at 12574. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12574)
open BstLean.Part268 (cell12574)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12574 (gMinus 12574) (1 - (cell12574 i).lower) ≤ 1 ∧
    energyUpper 12574 (gMinus 12574) (BstLean.Part211.gPlus 12574)
      (finiteEnergy 12574 12574 0.011) (1 - (cell12574 i).lower) ≤
      (cell12574 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨10,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨11,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨12,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨13,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨14,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨15,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨16,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨17,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨18,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨19,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨20,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨21,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨22,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨23,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨24,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨25,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨26,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨27,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨28,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨29,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨30,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨31,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨32,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨33,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨34,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨35,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨36,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨37,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨38,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨39,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨40,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨41,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨42,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨43,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨44,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨45,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨46,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨47,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨48,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨49,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨50,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨51,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12574) (by norm_num)
        (q := 1 - (cell12574 ⟨52,by decide⟩).lower)
        (by norm_num [cell12574]) (by norm_num [cell12574])
      exact ⟨E.1,E.2.trans (by norm_num [cell12574])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12574

/-! Source-cell containment and simple scalar guards at 12574. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12574)
open BstLean.Part268 (cell12574)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12574 ⟨10,by decide⟩).lower ∧ (cell12574 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12574 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12574 ⟨11,by decide⟩).lower ∧ (cell12574 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12574 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12574 ⟨12,by decide⟩).lower ∧ (cell12574 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12574 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12574 ⟨13,by decide⟩).lower ∧ (cell12574 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12574 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12574 ⟨14,by decide⟩).lower ∧ (cell12574 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12574 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12574 ⟨15,by decide⟩).lower ∧ (cell12574 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12574 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12574 ⟨16,by decide⟩).lower ∧ (cell12574 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12574 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12574 ⟨17,by decide⟩).lower ∧ (cell12574 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12574 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12574 ⟨18,by decide⟩).lower ∧ (cell12574 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12574 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12574 ⟨19,by decide⟩).lower ∧ (cell12574 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12574 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12574 ⟨20,by decide⟩).lower ∧ (cell12574 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12574 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12574 ⟨21,by decide⟩).lower ∧ (cell12574 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12574 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12574 ⟨22,by decide⟩).lower ∧ (cell12574 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12574 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12574 ⟨23,by decide⟩).lower ∧ (cell12574 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12574 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12574 ⟨24,by decide⟩).lower ∧ (cell12574 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12574 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12574 ⟨25,by decide⟩).lower ∧ (cell12574 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12574 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12574 ⟨26,by decide⟩).lower ∧ (cell12574 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12574 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12574 ⟨27,by decide⟩).lower ∧ (cell12574 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12574 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12574 ⟨28,by decide⟩).lower ∧ (cell12574 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12574 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12574 ⟨29,by decide⟩).lower ∧ (cell12574 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12574 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12574 ⟨30,by decide⟩).lower ∧ (cell12574 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12574 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12574 ⟨31,by decide⟩).lower ∧ (cell12574 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12574 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12574 ⟨32,by decide⟩).lower ∧ (cell12574 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12574 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12574 ⟨33,by decide⟩).lower ∧ (cell12574 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12574 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12574 ⟨34,by decide⟩).lower ∧ (cell12574 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12574 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12574 ⟨35,by decide⟩).lower ∧ (cell12574 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12574 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12574 ⟨36,by decide⟩).lower ∧ (cell12574 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12574 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12574 ⟨37,by decide⟩).lower ∧ (cell12574 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12574 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12574 ⟨38,by decide⟩).lower ∧ (cell12574 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12574 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12574 ⟨39,by decide⟩).lower ∧ (cell12574 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12574 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12574 ⟨40,by decide⟩).lower ∧ (cell12574 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12574 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12574 ⟨41,by decide⟩).lower ∧ (cell12574 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12574 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12574 ⟨42,by decide⟩).lower ∧ (cell12574 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12574 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12574 ⟨43,by decide⟩).lower ∧ (cell12574 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12574 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12574 ⟨44,by decide⟩).lower ∧ (cell12574 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12574 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12574 ⟨45,by decide⟩).lower ∧ (cell12574 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12574 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12574 ⟨46,by decide⟩).lower ∧ (cell12574 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12574 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12574 ⟨47,by decide⟩).lower ∧ (cell12574 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12574 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12574 ⟨48,by decide⟩).lower ∧ (cell12574 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12574 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12574 ⟨49,by decide⟩).lower ∧ (cell12574 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12574 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12574 ⟨50,by decide⟩).lower ∧ (cell12574 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12574 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12574 ⟨51,by decide⟩).lower ∧ (cell12574 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12574 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12574 ⟨52,by decide⟩).lower ∧ (cell12574 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12574 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12574 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12574 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12574,cell12574,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12574 i).lower ∧
    (cell12574 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12574 i).upper ≤ (0.532 : ℝ) ∧
    (cell12574 i).centre ≤ (0.1 : ℝ) ∧ (cell12574 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12574 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12574 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12574

/-! The local source numeric instances at 12574 have no network premises. -/
namespace BstLean.Part269.N12574
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12574)
open BstLean.Part268 (cell12574)

noncomputable def sourceNumerics12574 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12574 (cell12574 i)
      scalarRow12574.M scalarRow12574.H scalarRow12574.xi := by
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
    energy_allowance := scalarRow12574.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12574]
    centre_nonneg := (scalarRow12574.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12574])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12574