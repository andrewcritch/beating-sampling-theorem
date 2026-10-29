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
import BstLean.Part269Direction15
import BstLean.Part269Shared15
import BstLean.Part269Finite
import BstLean.Part269Rows15
import BstLean.Part269Source
/-! Actual 12738 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12738 ≤ (1.035755298636 : ℝ) := by
  have hr : (112.862748504544 : ℝ) ≤ √(12738 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.862748504544 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12738 12738 (11 / 1000) ≤
    (0.008469464290 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12738) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.862748504544 : ℝ) ≤ √(12738 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12738)
  have hdiv : K / √(12738 : ℝ) ≤ K / 112.862748504544 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.862748504544 ≤ (0.008469464290 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12738.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12738 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12738 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12738 := gPlus_lower 12738
end BstLean.Part269.N12738

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12738
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035755298635 : ℝ) ≤ wn 12738 := by
  have hn : √(12738 : ℝ) ≤ 112.862748504545 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12738 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.862748504545 ≤ 2 / √(12738 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251116385 : ℝ) ≤ rhoBar 12738 BstLean.Part154.csC ∧
    rhoBar 12738 BstLean.Part154.csC ≤ 0.000251116773 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035755298635 : ℝ) / (1.295212 * 12738) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035755298636 : ℝ) / (1.29521 * 12738) := by gcongr
      _ ≤ (0.000251116773 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12738 BstLean.Part154.csC) ≤ 0.001004530152 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12738 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) ≤ 0.000191804658 ∧
    cc1 (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) ≤ 0.000122046583 ∧
    cc2 (rhoBar 12738 BstLean.Part154.csC) ≤ 0.000070848983 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12738 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12738 BstLean.Part154.csC * nuR (rhoBar 12738 BstLean.Part154.csC)) ≤ 0.000502249311 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251116773 : ℝ) * 0.001004530152 := by gcongr
      _ ≤ (0.000502249311 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12738 BstLean.Part154.csC) * nuR (rhoBar 12738 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004530152 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12738 BstLean.Part154.csC) * rhoBar 12738 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251116773 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251116773 / 2 + 0.399 * 0.001004530152 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191804658 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502249311 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122046583 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251116773 / 1.414213562 := by gcongr
      _ ≤ (0.000070848983 : ℝ) := by norm_num

end BstLean.Part269.N12738

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12738
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) ≤ 1.58874E-7 := by
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12738 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12738 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191804658 : ℝ) ^ 2 + 0.000122046583 ^ 2 + 3 * 0.000070848983 ^ 2 +
        2 * 0.797885 * 0.000191804658 * 0.000122046583 + 2 * 0.000191804658 * 0.000070848983 +
        4 * 0.797885 * 0.000122046583 * 0.000070848983 := by gcongr
    _ ≤ (1.58874E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12738 BstLean.Part154.csC Θ ≤ 0.002621168465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12738 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12738 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035755298636 * 1.58874E-7 / (0.000251116385 : ℝ) := by gcongr
    _ ≤ 0.002621168465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12738 BstLean.Part154.csC Θ ≤ 0.002908180212 + 0.000662327962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12738 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035755298636 : ℝ) * ((2 * Θ * 0.000251116773 +
        (6863 / 10000) * 0.000251116773 * 12738 * 0.001004530152) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002908180212 + 0.000662327962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12738 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12738 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12738 0.011 Θ ∧ gammaRatio 12738 0.011 Θ ≤ 0.000086327453 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12738 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035755298636 : ℝ) * 0.525 / ((1 - 0.011) * 12738) := by gcongr
      _ ≤ (0.000086327453 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12738 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12738 0.011 Θ) :=
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
    badAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12738 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12738 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12738 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12738 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12738 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12738 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12738 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12738 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12738 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12738 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035755298636 : ℝ) * 12738 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003467264443 + 0.003283496427 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12738

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12738
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12738 BstLean.Part154.csC) (piBar (rhoBar 12738 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12738 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12738 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12738 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12738 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12738 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12738 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12738 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12738 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12738 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052405120474 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12738) ≤ 0.010581326407 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12738 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035755298636)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010581326407 + 2 * 0.737676 / 12738) := by gcongr
    _ ≤ (0.052405120474 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12738 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12738

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12738
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505281637 : ℝ) ≤ plow 12738 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12738) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697700068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376113445) : eMP 12738 0.011 xi bn ≤ 0.001184752113 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12738 : ℝ) * (1 - 0.011))) ≤ 0.000585805320 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376113445 / (12738 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585805320 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585805320 : ℝ) + 3.141593 * 0.052697700068 / (12738 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184752113 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697700068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376113445) : PiBarMP 12738 12 0.011 xi bn ≤ 0.161007688046 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12738 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037096003087 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.240286884879 : ℝ) ≤ √((12738 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.862748504544 : ℝ) ≤ √(12738 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12738) ≤ 0.123445587206 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037096003087 + 0.052697700068 * 1.772454 / (2 * (112.240286884879 : ℝ))) * (1 + 0.001184752113) +
        8 / (12738 * 112.862748504544) + 0.123445587206 := by gcongr
    _ ≤ (0.161007688046 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697700068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376113445) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281964916754) :
    parallelOracle 12738 0.011 xi bn cd ≤ 0.161994902753 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12738 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12738 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505281637 : ℝ) ≤ plow 12738 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.862748504544 : ℝ) ≤ √(12738 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281964916754 : ℝ) / (2 * 0.560505281637 * 112.862748504544)) * 0.161007688046 +
        0.281964916754 ^ 2 / (2 * 0.560505281637 * 112.862748504544) := by gcongr
    _ ≤ (0.161994902753 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697700068) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376113445)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281964916754) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12738 12738 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505281637 : ℝ) ≤ plow 12738 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.862748504544 : ℝ) ≤ √(12738 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12738 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12738 Θ 1.22 ≤ 0.011749673986 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.862748504544 := by gcongr <;> linarith
      _ ≤ (0.011749673986 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12738 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12738 12738 0.011 ≤ 0.008469464290 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12738 12738 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12738 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12738 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12738 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12738 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161994902753 + 0.011749673986 + (0.008469464290 : ℝ) *
        (1 + 2 * (0.281964916754 + 0.011749673986) / (0.560505281637 * 112.862748504544))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12738]

end BstLean.Part269.N12738

/-! The original eight local profiles supply actual 12738 moment certificates. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12738 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052697700068 ∧
    0 ≤ bN 12738 BstLean.Part154.csC (groupTheta g) ∧ bN 12738 BstLean.Part154.csC (groupTheta g) ≤ 0.001376113445 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12738 12738 0.011
      (momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12738 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12738 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12738 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229559796280 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12738 0.011
      (momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12738 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12738
/-! The actual computed-centre upper energy formula at 12738. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12738

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12738)
open BstLean.Part268 (cell12738)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085380209705
  | 2 => 0.086320954585
  | 3 => 0.087259549508
  | 4 => 0.088197345623
  | 5 => 0.089135979399
  | 6 => 0.090077415278
  | 7 => 0.091023992401
  | 8 => 0.091978475453
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12738 12738 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12738 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12738

/-! Actual upper energy certificates on all 43 source endpoints at 12738. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12738)
open BstLean.Part268 (cell12738)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12738 (gMinus 12738) (1 - (cell12738 i).lower) ≤ 1 ∧
    energyUpper 12738 (gMinus 12738) (BstLean.Part211.gPlus 12738)
      (finiteEnergy 12738 12738 0.011) (1 - (cell12738 i).lower) ≤
      (cell12738 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨10,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨11,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨12,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨13,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨14,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨15,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨16,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨17,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨18,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨19,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨20,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨21,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨22,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨23,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨24,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨25,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨26,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨27,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨28,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨29,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨30,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨31,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨32,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨33,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨34,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨35,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨36,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨37,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨38,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨39,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨40,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨41,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨42,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨43,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨44,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨45,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨46,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨47,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨48,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨49,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨50,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨51,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12738) (by norm_num)
        (q := 1 - (cell12738 ⟨52,by decide⟩).lower)
        (by norm_num [cell12738]) (by norm_num [cell12738])
      exact ⟨E.1,E.2.trans (by norm_num [cell12738])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12738

/-! Source-cell containment and simple scalar guards at 12738. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12738)
open BstLean.Part268 (cell12738)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12738 ⟨10,by decide⟩).lower ∧ (cell12738 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12738 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12738 ⟨11,by decide⟩).lower ∧ (cell12738 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12738 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12738 ⟨12,by decide⟩).lower ∧ (cell12738 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12738 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12738 ⟨13,by decide⟩).lower ∧ (cell12738 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12738 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12738 ⟨14,by decide⟩).lower ∧ (cell12738 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12738 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12738 ⟨15,by decide⟩).lower ∧ (cell12738 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12738 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12738 ⟨16,by decide⟩).lower ∧ (cell12738 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12738 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12738 ⟨17,by decide⟩).lower ∧ (cell12738 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12738 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12738 ⟨18,by decide⟩).lower ∧ (cell12738 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12738 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12738 ⟨19,by decide⟩).lower ∧ (cell12738 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12738 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12738 ⟨20,by decide⟩).lower ∧ (cell12738 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12738 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12738 ⟨21,by decide⟩).lower ∧ (cell12738 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12738 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12738 ⟨22,by decide⟩).lower ∧ (cell12738 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12738 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12738 ⟨23,by decide⟩).lower ∧ (cell12738 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12738 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12738 ⟨24,by decide⟩).lower ∧ (cell12738 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12738 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12738 ⟨25,by decide⟩).lower ∧ (cell12738 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12738 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12738 ⟨26,by decide⟩).lower ∧ (cell12738 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12738 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12738 ⟨27,by decide⟩).lower ∧ (cell12738 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12738 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12738 ⟨28,by decide⟩).lower ∧ (cell12738 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12738 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12738 ⟨29,by decide⟩).lower ∧ (cell12738 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12738 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12738 ⟨30,by decide⟩).lower ∧ (cell12738 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12738 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12738 ⟨31,by decide⟩).lower ∧ (cell12738 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12738 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12738 ⟨32,by decide⟩).lower ∧ (cell12738 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12738 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12738 ⟨33,by decide⟩).lower ∧ (cell12738 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12738 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12738 ⟨34,by decide⟩).lower ∧ (cell12738 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12738 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12738 ⟨35,by decide⟩).lower ∧ (cell12738 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12738 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12738 ⟨36,by decide⟩).lower ∧ (cell12738 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12738 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12738 ⟨37,by decide⟩).lower ∧ (cell12738 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12738 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12738 ⟨38,by decide⟩).lower ∧ (cell12738 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12738 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12738 ⟨39,by decide⟩).lower ∧ (cell12738 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12738 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12738 ⟨40,by decide⟩).lower ∧ (cell12738 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12738 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12738 ⟨41,by decide⟩).lower ∧ (cell12738 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12738 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12738 ⟨42,by decide⟩).lower ∧ (cell12738 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12738 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12738 ⟨43,by decide⟩).lower ∧ (cell12738 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12738 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12738 ⟨44,by decide⟩).lower ∧ (cell12738 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12738 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12738 ⟨45,by decide⟩).lower ∧ (cell12738 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12738 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12738 ⟨46,by decide⟩).lower ∧ (cell12738 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12738 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12738 ⟨47,by decide⟩).lower ∧ (cell12738 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12738 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12738 ⟨48,by decide⟩).lower ∧ (cell12738 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12738 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12738 ⟨49,by decide⟩).lower ∧ (cell12738 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12738 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12738 ⟨50,by decide⟩).lower ∧ (cell12738 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12738 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12738 ⟨51,by decide⟩).lower ∧ (cell12738 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12738 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12738 ⟨52,by decide⟩).lower ∧ (cell12738 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12738 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12738 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12738 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12738,cell12738,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12738 i).lower ∧
    (cell12738 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12738 i).upper ≤ (0.532 : ℝ) ∧
    (cell12738 i).centre ≤ (0.1 : ℝ) ∧ (cell12738 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12738 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12738 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12738

/-! The local source numeric instances at 12738 have no network premises. -/
namespace BstLean.Part269.N12738
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12738)
open BstLean.Part268 (cell12738)

noncomputable def sourceNumerics12738 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12738 (cell12738 i)
      scalarRow12738.M scalarRow12738.H scalarRow12738.xi := by
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
    energy_allowance := scalarRow12738.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12738]
    centre_nonneg := (scalarRow12738.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12738])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12738
/-! Actual 12739 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12739 ≤ (1.035753882904 : ℝ) := by
  have hr : (112.867178577299 : ℝ) ≤ √(12739 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.867178577299 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12739 12739 (11 / 1000) ≤
    (0.008469131859 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12739) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.867178577299 : ℝ) ≤ √(12739 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12739)
  have hdiv : K / √(12739 : ℝ) ≤ K / 112.867178577299 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.867178577299 ≤ (0.008469131859 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12739.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12739 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12739 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12739 := gPlus_lower 12739
end BstLean.Part269.N12739

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12739
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035753882903 : ℝ) ≤ wn 12739 := by
  have hn : √(12739 : ℝ) ≤ 112.867178577300 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12739 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.867178577300 ≤ 2 / √(12739 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251096329 : ℝ) ≤ rhoBar 12739 BstLean.Part154.csC ∧
    rhoBar 12739 BstLean.Part154.csC ≤ 0.000251096718 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035753882903 : ℝ) / (1.295212 * 12739) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035753882904 : ℝ) / (1.29521 * 12739) := by gcongr
      _ ≤ (0.000251096718 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12739 BstLean.Part154.csC) ≤ 0.001004449922 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12739 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) ≤ 0.000191789339 ∧
    cc1 (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) ≤ 0.000122036836 ∧
    cc2 (rhoBar 12739 BstLean.Part154.csC) ≤ 0.000070843325 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12739 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12739 BstLean.Part154.csC * nuR (rhoBar 12739 BstLean.Part154.csC)) ≤ 0.000502209199 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251096718 : ℝ) * 0.001004449922 := by gcongr
      _ ≤ (0.000502209199 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12739 BstLean.Part154.csC) * nuR (rhoBar 12739 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004449922 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12739 BstLean.Part154.csC) * rhoBar 12739 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251096718 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251096718 / 2 + 0.399 * 0.001004449922 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191789339 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502209199 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122036836 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251096718 / 1.414213562 := by gcongr
      _ ≤ (0.000070843325 : ℝ) := by norm_num

end BstLean.Part269.N12739

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12739
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) ≤ 1.58849E-7 := by
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12739 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12739 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191789339 : ℝ) ^ 2 + 0.000122036836 ^ 2 + 3 * 0.000070843325 ^ 2 +
        2 * 0.797885 * 0.000191789339 * 0.000122036836 + 2 * 0.000191789339 * 0.000070843325 +
        4 * 0.797885 * 0.000122036836 * 0.000070843325 := by gcongr
    _ ≤ (1.58849E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12739 BstLean.Part154.csC Θ ≤ 0.002620961752 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12739 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12739 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035753882904 * 1.58849E-7 / (0.000251096329 : ℝ) := by gcongr
    _ ≤ 0.002620961752 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12739 BstLean.Part154.csC Θ ≤ 0.002907939999 + 0.000662274161 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12739 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035753882904 : ℝ) * ((2 * Θ * 0.000251096718 +
        (6863 / 10000) * 0.000251096718 * 12739 * 0.001004449922) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002907939999 + 0.000662274161 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12739 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12739 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12739 0.011 Θ ∧ gammaRatio 12739 0.011 Θ ≤ 0.000086320559 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12739 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035753882904 : ℝ) * 0.525 / ((1 - 0.011) * 12739) := by gcongr
      _ ≤ (0.000086320559 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12739 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12739 0.011 Θ) :=
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
    badAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12739 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12739 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12739 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12739 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12739 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12739 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12739 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12739 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12739 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12739 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035753882904 : ℝ) * 12739 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003467024230 + 0.003283235913 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12739

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12739
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12739 BstLean.Part154.csC) (piBar (rhoBar 12739 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12739 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12739 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12739 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12739 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12739 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12739 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12739 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12739 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12739 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052403041283 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12739) ≤ 0.010580911086 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12739 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035753882904)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010580911086 + 2 * 0.737676 / 12739) := by gcongr
    _ ≤ (0.052403041283 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12739 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12739

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12739
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505326587 : ℝ) ≤ plow 12739 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12739) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697323085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376004920) : eMP 12739 0.011 xi bn ≤ 0.001184658804 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12739 : ℝ) * (1 - 0.011))) ≤ 0.000585759228 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001376004920 / (12739 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585759228 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585759228 : ℝ) + 3.141593 * 0.052697323085 / (12739 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184658804 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697323085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376004920) : PiBarMP 12739 12 0.011 xi bn ≤ 0.161001354761 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12739 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037094540300 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.244692524858 : ℝ) ≤ √((12739 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.867178577299 : ℝ) ≤ √(12739 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12739) ≤ 0.123440741927 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037094540300 + 0.052697323085 * 1.772454 / (2 * (112.244692524858 : ℝ))) * (1 + 0.001184658804) +
        8 / (12739 * 112.867178577299) + 0.123440741927 := by gcongr
    _ ≤ (0.161001354761 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697323085)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376004920) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281962016462) :
    parallelOracle 12739 0.011 xi bn cd ≤ 0.161988499909 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12739 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12739 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505326587 : ℝ) ≤ plow 12739 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.867178577299 : ℝ) ≤ √(12739 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281962016462 : ℝ) / (2 * 0.560505326587 * 112.867178577299)) * 0.161001354761 +
        0.281962016462 ^ 2 / (2 * 0.560505326587 * 112.867178577299) := by gcongr
    _ ≤ (0.161988499909 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052697323085) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001376004920)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281962016462) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12739 12739 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505326587 : ℝ) ≤ plow 12739 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.867178577299 : ℝ) ≤ √(12739 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12739 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12739 Θ 1.22 ≤ 0.011749212807 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.867178577299 := by gcongr <;> linarith
      _ ≤ (0.011749212807 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12739 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12739 12739 0.011 ≤ 0.008469131859 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12739 12739 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12739 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12739 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12739 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12739 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161988499909 + 0.011749212807 + (0.008469131859 : ℝ) *
        (1 + 2 * (0.281962016462 + 0.011749212807) / (0.560505326587 * 112.867178577299))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12739]

end BstLean.Part269.N12739

/-! The original eight local profiles supply actual 12739 moment certificates. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12739 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052697323085 ∧
    0 ≤ bN 12739 BstLean.Part154.csC (groupTheta g) ∧ bN 12739 BstLean.Part154.csC (groupTheta g) ≤ 0.001376004920 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12739 12739 0.011
      (momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12739 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12739 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12739 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229558975179 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12739 0.011
      (momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12739 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12739
/-! The actual computed-centre upper energy formula at 12739. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12739

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12739)
open BstLean.Part268 (cell12739)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085377334342
  | 2 => 0.086318027314
  | 3 => 0.087256562906
  | 4 => 0.088194290546
  | 5 => 0.089132844677
  | 6 => 0.090074187371
  | 7 => 0.091020655015
  | 8 => 0.091975009112
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12739 12739 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12739 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12739

/-! Actual upper energy certificates on all 43 source endpoints at 12739. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12739)
open BstLean.Part268 (cell12739)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12739 (gMinus 12739) (1 - (cell12739 i).lower) ≤ 1 ∧
    energyUpper 12739 (gMinus 12739) (BstLean.Part211.gPlus 12739)
      (finiteEnergy 12739 12739 0.011) (1 - (cell12739 i).lower) ≤
      (cell12739 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨10,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨11,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨12,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨13,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨14,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨15,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨16,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨17,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨18,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨19,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨20,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨21,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨22,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨23,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨24,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨25,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨26,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨27,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨28,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨29,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨30,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨31,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨32,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨33,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨34,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨35,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨36,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨37,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨38,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨39,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨40,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨41,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨42,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨43,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨44,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨45,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨46,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨47,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨48,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨49,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨50,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨51,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12739) (by norm_num)
        (q := 1 - (cell12739 ⟨52,by decide⟩).lower)
        (by norm_num [cell12739]) (by norm_num [cell12739])
      exact ⟨E.1,E.2.trans (by norm_num [cell12739])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12739

/-! Source-cell containment and simple scalar guards at 12739. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12739)
open BstLean.Part268 (cell12739)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12739 ⟨10,by decide⟩).lower ∧ (cell12739 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12739 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12739 ⟨11,by decide⟩).lower ∧ (cell12739 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12739 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12739 ⟨12,by decide⟩).lower ∧ (cell12739 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12739 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12739 ⟨13,by decide⟩).lower ∧ (cell12739 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12739 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12739 ⟨14,by decide⟩).lower ∧ (cell12739 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12739 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12739 ⟨15,by decide⟩).lower ∧ (cell12739 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12739 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12739 ⟨16,by decide⟩).lower ∧ (cell12739 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12739 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12739 ⟨17,by decide⟩).lower ∧ (cell12739 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12739 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12739 ⟨18,by decide⟩).lower ∧ (cell12739 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12739 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12739 ⟨19,by decide⟩).lower ∧ (cell12739 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12739 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12739 ⟨20,by decide⟩).lower ∧ (cell12739 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12739 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12739 ⟨21,by decide⟩).lower ∧ (cell12739 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12739 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12739 ⟨22,by decide⟩).lower ∧ (cell12739 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12739 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12739 ⟨23,by decide⟩).lower ∧ (cell12739 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12739 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12739 ⟨24,by decide⟩).lower ∧ (cell12739 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12739 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12739 ⟨25,by decide⟩).lower ∧ (cell12739 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12739 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12739 ⟨26,by decide⟩).lower ∧ (cell12739 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12739 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12739 ⟨27,by decide⟩).lower ∧ (cell12739 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12739 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12739 ⟨28,by decide⟩).lower ∧ (cell12739 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12739 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12739 ⟨29,by decide⟩).lower ∧ (cell12739 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12739 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12739 ⟨30,by decide⟩).lower ∧ (cell12739 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12739 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12739 ⟨31,by decide⟩).lower ∧ (cell12739 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12739 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12739 ⟨32,by decide⟩).lower ∧ (cell12739 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12739 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12739 ⟨33,by decide⟩).lower ∧ (cell12739 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12739 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12739 ⟨34,by decide⟩).lower ∧ (cell12739 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12739 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12739 ⟨35,by decide⟩).lower ∧ (cell12739 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12739 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12739 ⟨36,by decide⟩).lower ∧ (cell12739 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12739 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12739 ⟨37,by decide⟩).lower ∧ (cell12739 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12739 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12739 ⟨38,by decide⟩).lower ∧ (cell12739 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12739 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12739 ⟨39,by decide⟩).lower ∧ (cell12739 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12739 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12739 ⟨40,by decide⟩).lower ∧ (cell12739 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12739 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12739 ⟨41,by decide⟩).lower ∧ (cell12739 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12739 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12739 ⟨42,by decide⟩).lower ∧ (cell12739 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12739 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12739 ⟨43,by decide⟩).lower ∧ (cell12739 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12739 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12739 ⟨44,by decide⟩).lower ∧ (cell12739 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12739 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12739 ⟨45,by decide⟩).lower ∧ (cell12739 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12739 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12739 ⟨46,by decide⟩).lower ∧ (cell12739 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12739 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12739 ⟨47,by decide⟩).lower ∧ (cell12739 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12739 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12739 ⟨48,by decide⟩).lower ∧ (cell12739 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12739 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12739 ⟨49,by decide⟩).lower ∧ (cell12739 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12739 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12739 ⟨50,by decide⟩).lower ∧ (cell12739 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12739 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12739 ⟨51,by decide⟩).lower ∧ (cell12739 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12739 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12739 ⟨52,by decide⟩).lower ∧ (cell12739 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12739 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12739 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12739 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12739,cell12739,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12739 i).lower ∧
    (cell12739 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12739 i).upper ≤ (0.532 : ℝ) ∧
    (cell12739 i).centre ≤ (0.1 : ℝ) ∧ (cell12739 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12739 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12739 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12739

/-! The local source numeric instances at 12739 have no network premises. -/
namespace BstLean.Part269.N12739
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12739)
open BstLean.Part268 (cell12739)

noncomputable def sourceNumerics12739 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12739 (cell12739 i)
      scalarRow12739.M scalarRow12739.H scalarRow12739.xi := by
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
    energy_allowance := scalarRow12739.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12739]
    centre_nonneg := (scalarRow12739.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12739])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12739
/-! Actual 12740 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12740 ≤ (1.035752467340 : ℝ) := by
  have hr : (112.871608476179 : ℝ) ≤ √(12740 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.871608476179 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12740 12740 (11 / 1000) ≤
    (0.008468799466 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12740) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.871608476179 : ℝ) ≤ √(12740 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12740)
  have hdiv : K / √(12740 : ℝ) ≤ K / 112.871608476179 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.871608476179 ≤ (0.008468799466 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12740.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12740 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12740 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12740 := gPlus_lower 12740
end BstLean.Part269.N12740

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12740
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035752467339 : ℝ) ≤ wn 12740 := by
  have hn : √(12740 : ℝ) ≤ 112.871608476180 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12740 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.871608476180 ≤ 2 / √(12740 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251076277 : ℝ) ≤ rhoBar 12740 BstLean.Part154.csC ∧
    rhoBar 12740 BstLean.Part154.csC ≤ 0.000251076665 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035752467339 : ℝ) / (1.295212 * 12740) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035752467340 : ℝ) / (1.29521 * 12740) := by gcongr
      _ ≤ (0.000251076665 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12740 BstLean.Part154.csC) ≤ 0.001004369700 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12740 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) ≤ 0.000191774022 ∧
    cc1 (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) ≤ 0.000122027089 ∧
    cc2 (rhoBar 12740 BstLean.Part154.csC) ≤ 0.000070837667 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12740 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12740 BstLean.Part154.csC * nuR (rhoBar 12740 BstLean.Part154.csC)) ≤ 0.000502169090 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251076665 : ℝ) * 0.001004369700 := by gcongr
      _ ≤ (0.000502169090 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12740 BstLean.Part154.csC) * nuR (rhoBar 12740 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004369700 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12740 BstLean.Part154.csC) * rhoBar 12740 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251076665 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251076665 / 2 + 0.399 * 0.001004369700 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191774022 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502169090 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122027089 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251076665 / 1.414213562 := by gcongr
      _ ≤ (0.000070837667 : ℝ) := by norm_num

end BstLean.Part269.N12740

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12740
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) ≤ 1.58824E-7 := by
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12740 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12740 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191774022 : ℝ) ^ 2 + 0.000122027089 ^ 2 + 3 * 0.000070837667 ^ 2 +
        2 * 0.797885 * 0.000191774022 * 0.000122027089 + 2 * 0.000191774022 * 0.000070837667 +
        4 * 0.797885 * 0.000122027089 * 0.000070837667 := by gcongr
    _ ≤ (1.58824E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12740 BstLean.Part154.csC Θ ≤ 0.002620754965 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12740 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12740 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035752467340 * 1.58824E-7 / (0.000251076277 : ℝ) := by gcongr
    _ ≤ 0.002620754965 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12740 BstLean.Part154.csC Θ ≤ 0.002907699798 + 0.000662220366 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12740 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035752467340 : ℝ) * ((2 * Θ * 0.000251076665 +
        (6863 / 10000) * 0.000251076665 * 12740 * 0.001004369700) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002907699798 + 0.000662220366 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12740 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12740 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12740 0.011 Θ ∧ gammaRatio 12740 0.011 Θ ≤ 0.000086313665 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12740 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035752467340 : ℝ) * 0.525 / ((1 - 0.011) * 12740) := by gcongr
      _ ≤ (0.000086313665 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12740 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12740 0.011 Θ) :=
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
    badAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12740 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12740 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12740 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12740 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12740 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12740 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12740 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12740 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12740 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12740 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035752467340 : ℝ) * 12740 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003466784029 + 0.003282975331 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12740

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12740
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12740 BstLean.Part154.csC) (piBar (rhoBar 12740 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12740 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12740 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12740 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12740 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12740 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12740 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12740 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12740 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12740 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052400962344 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12740) ≤ 0.010580495815 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12740 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035752467340)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010580495815 + 2 * 0.737676 / 12740) := by gcongr
    _ ≤ (0.052400962344 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12740 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12740

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12740
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505371530 : ℝ) ≤ plow 12740 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12740) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696946078)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375896357) : eMP 12740 0.011 xi bn ≤ 0.001184565486 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12740 : ℝ) * (1 - 0.011))) ≤ 0.000585713132 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375896357 / (12740 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585713132 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585713132 : ℝ) + 3.141593 * 0.052696946078 / (12740 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184565486 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696946078)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375896357) : PiBarMP 12740 12 0.011 xi bn ≤ 0.160995021477 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12740 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037093076942 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.249097991921 : ℝ) ≤ √((12740 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.871608476179 : ℝ) ≤ √(12740 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12740) ≤ 0.123435897219 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037093076942 + 0.052696946078 * 1.772454 / (2 * (112.249097991921 : ℝ))) * (1 + 0.001184565486) +
        8 / (12740 * 112.871608476179) + 0.123435897219 := by gcongr
    _ ≤ (0.160995021477 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696946078)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375896357) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281959116367) :
    parallelOracle 12740 0.011 xi bn cd ≤ 0.161982097075 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12740 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12740 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505371530 : ℝ) ≤ plow 12740 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.871608476179 : ℝ) ≤ √(12740 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281959116367 : ℝ) / (2 * 0.560505371530 * 112.871608476179)) * 0.160995021477 +
        0.281959116367 ^ 2 / (2 * 0.560505371530 * 112.871608476179) := by gcongr
    _ ≤ (0.161982097075 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696946078) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375896357)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281959116367) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12740 12740 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505371530 : ℝ) ≤ plow 12740 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.871608476179 : ℝ) ≤ √(12740 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12740 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12740 Θ 1.22 ≤ 0.011748751683 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.871608476179 := by gcongr <;> linarith
      _ ≤ (0.011748751683 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12740 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12740 12740 0.011 ≤ 0.008468799466 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12740 12740 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12740 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12740 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12740 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12740 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161982097075 + 0.011748751683 + (0.008468799466 : ℝ) *
        (1 + 2 * (0.281959116367 + 0.011748751683) / (0.560505371530 * 112.871608476179))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12740]

end BstLean.Part269.N12740

/-! The original eight local profiles supply actual 12740 moment certificates. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12740 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052696946078 ∧
    0 ≤ bN 12740 BstLean.Part154.csC (groupTheta g) ∧ bN 12740 BstLean.Part154.csC (groupTheta g) ≤ 0.001375896357 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12740 12740 0.011
      (momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12740 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12740 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12740 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229558154023 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12740 0.011
      (momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12740 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12740
/-! The actual computed-centre upper energy formula at 12740. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12740

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12740)
open BstLean.Part268 (cell12740)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085374460021
  | 2 => 0.086315101128
  | 3 => 0.087253577440
  | 4 => 0.088191236670
  | 5 => 0.089129711235
  | 6 => 0.090070960839
  | 7 => 0.091017319120
  | 8 => 0.091971544401
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12740 12740 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12740 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12740

/-! Actual upper energy certificates on all 43 source endpoints at 12740. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12740)
open BstLean.Part268 (cell12740)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12740 (gMinus 12740) (1 - (cell12740 i).lower) ≤ 1 ∧
    energyUpper 12740 (gMinus 12740) (BstLean.Part211.gPlus 12740)
      (finiteEnergy 12740 12740 0.011) (1 - (cell12740 i).lower) ≤
      (cell12740 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨10,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨11,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨12,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨13,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨14,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨15,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨16,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨17,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨18,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨19,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨20,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨21,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨22,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨23,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨24,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨25,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨26,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨27,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨28,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨29,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨30,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨31,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨32,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨33,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨34,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨35,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨36,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨37,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨38,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨39,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨40,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨41,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨42,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨43,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨44,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨45,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨46,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨47,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨48,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨49,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨50,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨51,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12740) (by norm_num)
        (q := 1 - (cell12740 ⟨52,by decide⟩).lower)
        (by norm_num [cell12740]) (by norm_num [cell12740])
      exact ⟨E.1,E.2.trans (by norm_num [cell12740])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12740

/-! Source-cell containment and simple scalar guards at 12740. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12740)
open BstLean.Part268 (cell12740)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12740 ⟨10,by decide⟩).lower ∧ (cell12740 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12740 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12740 ⟨11,by decide⟩).lower ∧ (cell12740 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12740 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12740 ⟨12,by decide⟩).lower ∧ (cell12740 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12740 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12740 ⟨13,by decide⟩).lower ∧ (cell12740 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12740 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12740 ⟨14,by decide⟩).lower ∧ (cell12740 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12740 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12740 ⟨15,by decide⟩).lower ∧ (cell12740 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12740 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12740 ⟨16,by decide⟩).lower ∧ (cell12740 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12740 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12740 ⟨17,by decide⟩).lower ∧ (cell12740 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12740 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12740 ⟨18,by decide⟩).lower ∧ (cell12740 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12740 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12740 ⟨19,by decide⟩).lower ∧ (cell12740 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12740 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12740 ⟨20,by decide⟩).lower ∧ (cell12740 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12740 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12740 ⟨21,by decide⟩).lower ∧ (cell12740 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12740 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12740 ⟨22,by decide⟩).lower ∧ (cell12740 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12740 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12740 ⟨23,by decide⟩).lower ∧ (cell12740 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12740 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12740 ⟨24,by decide⟩).lower ∧ (cell12740 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12740 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12740 ⟨25,by decide⟩).lower ∧ (cell12740 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12740 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12740 ⟨26,by decide⟩).lower ∧ (cell12740 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12740 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12740 ⟨27,by decide⟩).lower ∧ (cell12740 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12740 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12740 ⟨28,by decide⟩).lower ∧ (cell12740 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12740 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12740 ⟨29,by decide⟩).lower ∧ (cell12740 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12740 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12740 ⟨30,by decide⟩).lower ∧ (cell12740 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12740 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12740 ⟨31,by decide⟩).lower ∧ (cell12740 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12740 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12740 ⟨32,by decide⟩).lower ∧ (cell12740 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12740 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12740 ⟨33,by decide⟩).lower ∧ (cell12740 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12740 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12740 ⟨34,by decide⟩).lower ∧ (cell12740 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12740 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12740 ⟨35,by decide⟩).lower ∧ (cell12740 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12740 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12740 ⟨36,by decide⟩).lower ∧ (cell12740 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12740 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12740 ⟨37,by decide⟩).lower ∧ (cell12740 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12740 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12740 ⟨38,by decide⟩).lower ∧ (cell12740 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12740 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12740 ⟨39,by decide⟩).lower ∧ (cell12740 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12740 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12740 ⟨40,by decide⟩).lower ∧ (cell12740 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12740 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12740 ⟨41,by decide⟩).lower ∧ (cell12740 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12740 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12740 ⟨42,by decide⟩).lower ∧ (cell12740 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12740 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12740 ⟨43,by decide⟩).lower ∧ (cell12740 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12740 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12740 ⟨44,by decide⟩).lower ∧ (cell12740 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12740 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12740 ⟨45,by decide⟩).lower ∧ (cell12740 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12740 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12740 ⟨46,by decide⟩).lower ∧ (cell12740 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12740 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12740 ⟨47,by decide⟩).lower ∧ (cell12740 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12740 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12740 ⟨48,by decide⟩).lower ∧ (cell12740 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12740 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12740 ⟨49,by decide⟩).lower ∧ (cell12740 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12740 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12740 ⟨50,by decide⟩).lower ∧ (cell12740 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12740 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12740 ⟨51,by decide⟩).lower ∧ (cell12740 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12740 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12740 ⟨52,by decide⟩).lower ∧ (cell12740 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12740 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12740 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12740 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12740,cell12740,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12740 i).lower ∧
    (cell12740 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12740 i).upper ≤ (0.532 : ℝ) ∧
    (cell12740 i).centre ≤ (0.1 : ℝ) ∧ (cell12740 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12740 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12740 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12740

/-! The local source numeric instances at 12740 have no network premises. -/
namespace BstLean.Part269.N12740
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12740)
open BstLean.Part268 (cell12740)

noncomputable def sourceNumerics12740 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12740 (cell12740 i)
      scalarRow12740.M scalarRow12740.H scalarRow12740.xi := by
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
    energy_allowance := scalarRow12740.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12740]
    centre_nonneg := (scalarRow12740.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12740])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12740
/-! Actual 12741 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12741 ≤ (1.035751051943 : ℝ) := by
  have hr : (112.876038201205 : ℝ) ≤ √(12741 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.876038201205 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12741 12741 (11 / 1000) ≤
    (0.008468467112 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12741) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.876038201205 : ℝ) ≤ √(12741 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12741)
  have hdiv : K / √(12741 : ℝ) ≤ K / 112.876038201205 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.876038201205 ≤ (0.008468467112 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12741.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12741 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12741 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12741 := gPlus_lower 12741
end BstLean.Part269.N12741

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12741
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035751051942 : ℝ) ≤ wn 12741 := by
  have hn : √(12741 : ℝ) ≤ 112.876038201206 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12741 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.876038201206 ≤ 2 / √(12741 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251056227 : ℝ) ≤ rhoBar 12741 BstLean.Part154.csC ∧
    rhoBar 12741 BstLean.Part154.csC ≤ 0.000251056616 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035751051942 : ℝ) / (1.295212 * 12741) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035751051943 : ℝ) / (1.29521 * 12741) := by gcongr
      _ ≤ (0.000251056616 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12741 BstLean.Part154.csC) ≤ 0.001004289494 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12741 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) ≤ 0.000191758708 ∧
    cc1 (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) ≤ 0.000122017345 ∧
    cc2 (rhoBar 12741 BstLean.Part154.csC) ≤ 0.000070832011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12741 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12741 BstLean.Part154.csC * nuR (rhoBar 12741 BstLean.Part154.csC)) ≤ 0.000502128990 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251056616 : ℝ) * 0.001004289494 := by gcongr
      _ ≤ (0.000502128990 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12741 BstLean.Part154.csC) * nuR (rhoBar 12741 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004289494 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12741 BstLean.Part154.csC) * rhoBar 12741 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251056616 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251056616 / 2 + 0.399 * 0.001004289494 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191758708 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502128990 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122017345 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251056616 / 1.414213562 := by gcongr
      _ ≤ (0.000070832011 : ℝ) := by norm_num

end BstLean.Part269.N12741

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12741
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) ≤ 1.58798E-7 := by
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12741 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12741 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191758708 : ℝ) ^ 2 + 0.000122017345 ^ 2 + 3 * 0.000070832011 ^ 2 +
        2 * 0.797885 * 0.000191758708 * 0.000122017345 + 2 * 0.000191758708 * 0.000070832011 +
        4 * 0.797885 * 0.000122017345 * 0.000070832011 := by gcongr
    _ ≤ (1.58798E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12741 BstLean.Part154.csC Θ ≤ 0.002620531624 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12741 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12741 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035751051943 * 1.58798E-7 / (0.000251056227 : ℝ) := by gcongr
    _ ≤ 0.002620531624 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12741 BstLean.Part154.csC Θ ≤ 0.002907459654 + 0.000662166581 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12741 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035751051943 : ℝ) * ((2 * Θ * 0.000251056616 +
        (6863 / 10000) * 0.000251056616 * 12741 * 0.001004289494) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002907459654 + 0.000662166581 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12741 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12741 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12741 0.011 Θ ∧ gammaRatio 12741 0.011 Θ ≤ 0.000086306773 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12741 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035751051943 : ℝ) * 0.525 / ((1 - 0.011) * 12741) := by gcongr
      _ ≤ (0.000086306773 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12741 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12741 0.011 Θ) :=
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
    badAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12741 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12741 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12741 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12741 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12741 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12741 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12741 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12741 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12741 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12741 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035751051943 : ℝ) * 12741 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003466543885 + 0.003282698205 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12741

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12741
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12741 BstLean.Part154.csC) (piBar (rhoBar 12741 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12741 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12741 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12741 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12741 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12741 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12741 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12741 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12741 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12741 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052398883648 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12741) ≤ 0.010580080592 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12741 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035751051943)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010580080592 + 2 * 0.737676 / 12741) := by gcongr
    _ ≤ (0.052398883648 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12741 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12741

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12741
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505416466 : ℝ) ≤ plow 12741 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12741) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696560443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375779103) : eMP 12741 0.011 xi bn ≤ 0.001184468473 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12741 : ℝ) * (1 - 0.011))) ≤ 0.000585665189 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375779103 / (12741 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585665189 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585665189 : ℝ) + 3.141593 * 0.052696560443 / (12741 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184468473 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696560443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375779103) : PiBarMP 12741 12 0.011 xi bn ≤ 0.160988571207 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12741 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037091496371 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.253503286089 : ℝ) ≤ √((12741 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.876038201205 : ℝ) ≤ √(12741 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12741) ≤ 0.123431053081 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037091496371 + 0.052696560443 * 1.772454 / (2 * (112.253503286089 : ℝ))) * (1 + 0.001184468473) +
        8 / (12741 * 112.876038201205) + 0.123431053081 := by gcongr
    _ ≤ (0.160988571207 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696560443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375779103) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281956197718) :
    parallelOracle 12741 0.011 xi bn cd ≤ 0.161975576895 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12741 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12741 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505416466 : ℝ) ≤ plow 12741 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.876038201205 : ℝ) ≤ √(12741 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281956197718 : ℝ) / (2 * 0.560505416466 * 112.876038201205)) * 0.160988571207 +
        0.281956197718 ^ 2 / (2 * 0.560505416466 * 112.876038201205) := by gcongr
    _ ≤ (0.161975576895 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696560443) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375779103)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281956197718) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12741 12741 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505416466 : ℝ) ≤ plow 12741 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.876038201205 : ℝ) ≤ √(12741 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12741 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12741 Θ 1.22 ≤ 0.011748290613 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.876038201205 := by gcongr <;> linarith
      _ ≤ (0.011748290613 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12741 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12741 12741 0.011 ≤ 0.008468467112 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12741 12741 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12741 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12741 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12741 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12741 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161975576895 + 0.011748290613 + (0.008468467112 : ℝ) *
        (1 + 2 * (0.281956197718 + 0.011748290613) / (0.560505416466 * 112.876038201205))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12741]

end BstLean.Part269.N12741

/-! The original eight local profiles supply actual 12741 moment certificates. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12741 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052696560443 ∧
    0 ≤ bN 12741 BstLean.Part154.csC (groupTheta g) ∧ bN 12741 BstLean.Part154.csC (groupTheta g) ≤ 0.001375779103 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12741 12741 0.011
      (momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12741 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12741 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12741 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229557314070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12741 0.011
      (momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12741 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12741
/-! The actual computed-centre upper energy formula at 12741. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12741

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12741)
open BstLean.Part268 (cell12741)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085371586741
  | 2 => 0.086312176025
  | 3 => 0.087250593110
  | 4 => 0.088188183994
  | 5 => 0.089126579070
  | 6 => 0.090067735680
  | 7 => 0.091013984713
  | 8 => 0.091968081319
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12741 12741 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12741 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12741

/-! Actual upper energy certificates on all 43 source endpoints at 12741. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12741)
open BstLean.Part268 (cell12741)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12741 (gMinus 12741) (1 - (cell12741 i).lower) ≤ 1 ∧
    energyUpper 12741 (gMinus 12741) (BstLean.Part211.gPlus 12741)
      (finiteEnergy 12741 12741 0.011) (1 - (cell12741 i).lower) ≤
      (cell12741 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨10,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨11,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨12,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨13,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨14,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨15,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨16,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨17,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨18,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨19,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨20,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨21,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨22,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨23,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨24,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨25,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨26,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨27,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨28,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨29,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨30,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨31,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨32,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨33,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨34,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨35,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨36,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨37,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨38,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨39,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨40,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨41,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨42,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨43,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨44,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨45,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨46,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨47,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨48,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨49,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨50,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨51,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12741) (by norm_num)
        (q := 1 - (cell12741 ⟨52,by decide⟩).lower)
        (by norm_num [cell12741]) (by norm_num [cell12741])
      exact ⟨E.1,E.2.trans (by norm_num [cell12741])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12741

/-! Source-cell containment and simple scalar guards at 12741. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12741)
open BstLean.Part268 (cell12741)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12741 ⟨10,by decide⟩).lower ∧ (cell12741 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12741 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12741 ⟨11,by decide⟩).lower ∧ (cell12741 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12741 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12741 ⟨12,by decide⟩).lower ∧ (cell12741 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12741 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12741 ⟨13,by decide⟩).lower ∧ (cell12741 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12741 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12741 ⟨14,by decide⟩).lower ∧ (cell12741 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12741 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12741 ⟨15,by decide⟩).lower ∧ (cell12741 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12741 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12741 ⟨16,by decide⟩).lower ∧ (cell12741 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12741 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12741 ⟨17,by decide⟩).lower ∧ (cell12741 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12741 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12741 ⟨18,by decide⟩).lower ∧ (cell12741 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12741 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12741 ⟨19,by decide⟩).lower ∧ (cell12741 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12741 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12741 ⟨20,by decide⟩).lower ∧ (cell12741 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12741 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12741 ⟨21,by decide⟩).lower ∧ (cell12741 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12741 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12741 ⟨22,by decide⟩).lower ∧ (cell12741 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12741 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12741 ⟨23,by decide⟩).lower ∧ (cell12741 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12741 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12741 ⟨24,by decide⟩).lower ∧ (cell12741 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12741 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12741 ⟨25,by decide⟩).lower ∧ (cell12741 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12741 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12741 ⟨26,by decide⟩).lower ∧ (cell12741 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12741 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12741 ⟨27,by decide⟩).lower ∧ (cell12741 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12741 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12741 ⟨28,by decide⟩).lower ∧ (cell12741 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12741 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12741 ⟨29,by decide⟩).lower ∧ (cell12741 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12741 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12741 ⟨30,by decide⟩).lower ∧ (cell12741 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12741 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12741 ⟨31,by decide⟩).lower ∧ (cell12741 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12741 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12741 ⟨32,by decide⟩).lower ∧ (cell12741 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12741 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12741 ⟨33,by decide⟩).lower ∧ (cell12741 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12741 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12741 ⟨34,by decide⟩).lower ∧ (cell12741 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12741 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12741 ⟨35,by decide⟩).lower ∧ (cell12741 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12741 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12741 ⟨36,by decide⟩).lower ∧ (cell12741 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12741 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12741 ⟨37,by decide⟩).lower ∧ (cell12741 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12741 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12741 ⟨38,by decide⟩).lower ∧ (cell12741 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12741 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12741 ⟨39,by decide⟩).lower ∧ (cell12741 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12741 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12741 ⟨40,by decide⟩).lower ∧ (cell12741 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12741 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12741 ⟨41,by decide⟩).lower ∧ (cell12741 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12741 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12741 ⟨42,by decide⟩).lower ∧ (cell12741 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12741 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12741 ⟨43,by decide⟩).lower ∧ (cell12741 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12741 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12741 ⟨44,by decide⟩).lower ∧ (cell12741 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12741 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12741 ⟨45,by decide⟩).lower ∧ (cell12741 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12741 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12741 ⟨46,by decide⟩).lower ∧ (cell12741 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12741 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12741 ⟨47,by decide⟩).lower ∧ (cell12741 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12741 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12741 ⟨48,by decide⟩).lower ∧ (cell12741 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12741 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12741 ⟨49,by decide⟩).lower ∧ (cell12741 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12741 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12741 ⟨50,by decide⟩).lower ∧ (cell12741 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12741 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12741 ⟨51,by decide⟩).lower ∧ (cell12741 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12741 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12741 ⟨52,by decide⟩).lower ∧ (cell12741 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12741 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12741 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12741 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12741,cell12741,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12741 i).lower ∧
    (cell12741 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12741 i).upper ≤ (0.532 : ℝ) ∧
    (cell12741 i).centre ≤ (0.1 : ℝ) ∧ (cell12741 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12741 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12741 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12741

/-! The local source numeric instances at 12741 have no network premises. -/
namespace BstLean.Part269.N12741
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12741)
open BstLean.Part268 (cell12741)

noncomputable def sourceNumerics12741 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12741 (cell12741 i)
      scalarRow12741.M scalarRow12741.H scalarRow12741.xi := by
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
    energy_allowance := scalarRow12741.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12741]
    centre_nonneg := (scalarRow12741.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12741])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12741
/-! Actual 12742 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12742 ≤ (1.035749636714 : ℝ) := by
  have hr : (112.880467752397 : ℝ) ≤ √(12742 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.880467752397 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12742 12742 (11 / 1000) ≤
    (0.008468134798 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12742) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.880467752397 : ℝ) ≤ √(12742 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12742)
  have hdiv : K / √(12742 : ℝ) ≤ K / 112.880467752397 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.880467752397 ≤ (0.008468134798 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12742.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12742 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12742 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12742 := gPlus_lower 12742
end BstLean.Part269.N12742

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12742
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035749636713 : ℝ) ≤ wn 12742 := by
  have hn : √(12742 : ℝ) ≤ 112.880467752398 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12742 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.880467752398 ≤ 2 / √(12742 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251036181 : ℝ) ≤ rhoBar 12742 BstLean.Part154.csC ∧
    rhoBar 12742 BstLean.Part154.csC ≤ 0.000251036570 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035749636713 : ℝ) / (1.295212 * 12742) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035749636714 : ℝ) / (1.29521 * 12742) := by gcongr
      _ ≤ (0.000251036570 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12742 BstLean.Part154.csC) ≤ 0.001004209300 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12742 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) ≤ 0.000191743396 ∧
    cc1 (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) ≤ 0.000122007602 ∧
    cc2 (rhoBar 12742 BstLean.Part154.csC) ≤ 0.000070826355 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12742 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12742 BstLean.Part154.csC * nuR (rhoBar 12742 BstLean.Part154.csC)) ≤ 0.000502088895 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251036570 : ℝ) * 0.001004209300 := by gcongr
      _ ≤ (0.000502088895 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12742 BstLean.Part154.csC) * nuR (rhoBar 12742 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004209300 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12742 BstLean.Part154.csC) * rhoBar 12742 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251036570 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251036570 / 2 + 0.399 * 0.001004209300 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191743396 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502088895 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122007602 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251036570 / 1.414213562 := by gcongr
      _ ≤ (0.000070826355 : ℝ) := by norm_num

end BstLean.Part269.N12742

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12742
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) ≤ 1.58773E-7 := by
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12742 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12742 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191743396 : ℝ) ^ 2 + 0.000122007602 ^ 2 + 3 * 0.000070826355 ^ 2 +
        2 * 0.797885 * 0.000191743396 * 0.000122007602 + 2 * 0.000191743396 * 0.000070826355 +
        4 * 0.797885 * 0.000122007602 * 0.000070826355 := by gcongr
    _ ≤ (1.58773E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12742 BstLean.Part154.csC Θ ≤ 0.002620324711 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12742 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12742 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035749636714 * 1.58773E-7 / (0.000251036181 : ℝ) := by gcongr
    _ ≤ 0.002620324711 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12742 BstLean.Part154.csC Θ ≤ 0.002907219545 + 0.000662112805 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12742 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035749636714 : ℝ) * ((2 * Θ * 0.000251036570 +
        (6863 / 10000) * 0.000251036570 * 12742 * 0.001004209300) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002907219545 + 0.000662112805 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12742 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12742 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12742 0.011 Θ ∧ gammaRatio 12742 0.011 Θ ≤ 0.000086299881 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12742 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035749636714 : ℝ) * 0.525 / ((1 - 0.011) * 12742) := by gcongr
      _ ≤ (0.000086299881 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12742 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12742 0.011 Θ) :=
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
    badAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12742 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12742 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12742 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12742 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12742 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12742 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12742 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12742 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12742 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12742 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035749636714 : ℝ) * 12742 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003466303776 + 0.003282437516 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12742

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12742
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12742 BstLean.Part154.csC) (piBar (rhoBar 12742 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12742 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12742 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12742 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12742 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12742 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12742 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12742 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12742 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12742 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052396805203 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12742) ≤ 0.010579665419 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12742 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035749636714)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010579665419 + 2 * 0.737676 / 12742) := by gcongr
    _ ≤ (0.052396805203 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12742 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12742

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12742
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505461395 : ℝ) ≤ plow 12742 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12742) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696183472)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375670474) : eMP 12742 0.011 xi bn ≤ 0.001184375142 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12742 : ℝ) * (1 - 0.011))) ≤ 0.000585619086 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375670474 / (12742 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585619086 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585619086 : ℝ) + 3.141593 * 0.052696183472 / (12742 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184375142 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696183472)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375670474) : PiBarMP 12742 12 0.011 xi bn ≤ 0.160982238059 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12742 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037090032004 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.257908407381 : ℝ) ≤ √((12742 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.880467752397 : ℝ) ≤ √(12742 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12742) ≤ 0.123426209514 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037090032004 + 0.052696183472 * 1.772454 / (2 * (112.257908407381 : ℝ))) * (1 + 0.001184375142) +
        8 / (12742 * 112.880467752397) + 0.123426209514 := by gcongr
    _ ≤ (0.160982238059 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696183472)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375670474) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281953298189) :
    parallelOracle 12742 0.011 xi bn cd ≤ 0.161969174215 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12742 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12742 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505461395 : ℝ) ≤ plow 12742 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.880467752397 : ℝ) ≤ √(12742 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281953298189 : ℝ) / (2 * 0.560505461395 * 112.880467752397)) * 0.160982238059 +
        0.281953298189 ^ 2 / (2 * 0.560505461395 * 112.880467752397) := by gcongr
    _ ≤ (0.161969174215 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052696183472) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375670474)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281953298189) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12742 12742 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505461395 : ℝ) ≤ plow 12742 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.880467752397 : ℝ) ≤ √(12742 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12742 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12742 Θ 1.22 ≤ 0.011747829598 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.880467752397 := by gcongr <;> linarith
      _ ≤ (0.011747829598 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12742 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12742 12742 0.011 ≤ 0.008468134798 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12742 12742 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12742 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12742 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12742 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12742 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161969174215 + 0.011747829598 + (0.008468134798 : ℝ) *
        (1 + 2 * (0.281953298189 + 0.011747829598) / (0.560505461395 * 112.880467752397))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12742]

end BstLean.Part269.N12742

/-! The original eight local profiles supply actual 12742 moment certificates. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12742 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052696183472 ∧
    0 ≤ bN 12742 BstLean.Part154.csC (groupTheta g) ∧ bN 12742 BstLean.Part154.csC (groupTheta g) ≤ 0.001375670474 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12742 12742 0.011
      (momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12742 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12742 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12742 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229556492986 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12742 0.011
      (momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12742 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12742
/-! The actual computed-centre upper energy formula at 12742. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12742

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12742)
open BstLean.Part268 (cell12742)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085368714501
  | 2 => 0.086309252004
  | 3 => 0.087247609915
  | 4 => 0.088185132516
  | 5 => 0.089123448182
  | 6 => 0.090064511894
  | 7 => 0.091010651795
  | 8 => 0.091964619863
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12742 12742 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12742 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12742

/-! Actual upper energy certificates on all 43 source endpoints at 12742. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12742)
open BstLean.Part268 (cell12742)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12742 (gMinus 12742) (1 - (cell12742 i).lower) ≤ 1 ∧
    energyUpper 12742 (gMinus 12742) (BstLean.Part211.gPlus 12742)
      (finiteEnergy 12742 12742 0.011) (1 - (cell12742 i).lower) ≤
      (cell12742 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨10,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨11,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨12,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨13,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨14,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨15,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨16,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨17,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨18,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨19,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨20,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨21,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨22,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨23,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨24,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨25,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨26,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨27,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨28,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨29,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨30,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨31,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨32,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨33,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨34,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨35,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨36,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨37,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨38,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨39,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨40,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨41,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨42,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨43,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨44,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨45,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨46,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨47,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨48,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨49,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨50,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨51,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12742) (by norm_num)
        (q := 1 - (cell12742 ⟨52,by decide⟩).lower)
        (by norm_num [cell12742]) (by norm_num [cell12742])
      exact ⟨E.1,E.2.trans (by norm_num [cell12742])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12742

/-! Source-cell containment and simple scalar guards at 12742. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12742)
open BstLean.Part268 (cell12742)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12742 ⟨10,by decide⟩).lower ∧ (cell12742 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12742 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12742 ⟨11,by decide⟩).lower ∧ (cell12742 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12742 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12742 ⟨12,by decide⟩).lower ∧ (cell12742 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12742 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12742 ⟨13,by decide⟩).lower ∧ (cell12742 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12742 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12742 ⟨14,by decide⟩).lower ∧ (cell12742 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12742 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12742 ⟨15,by decide⟩).lower ∧ (cell12742 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12742 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12742 ⟨16,by decide⟩).lower ∧ (cell12742 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12742 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12742 ⟨17,by decide⟩).lower ∧ (cell12742 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12742 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12742 ⟨18,by decide⟩).lower ∧ (cell12742 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12742 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12742 ⟨19,by decide⟩).lower ∧ (cell12742 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12742 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12742 ⟨20,by decide⟩).lower ∧ (cell12742 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12742 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12742 ⟨21,by decide⟩).lower ∧ (cell12742 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12742 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12742 ⟨22,by decide⟩).lower ∧ (cell12742 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12742 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12742 ⟨23,by decide⟩).lower ∧ (cell12742 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12742 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12742 ⟨24,by decide⟩).lower ∧ (cell12742 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12742 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12742 ⟨25,by decide⟩).lower ∧ (cell12742 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12742 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12742 ⟨26,by decide⟩).lower ∧ (cell12742 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12742 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12742 ⟨27,by decide⟩).lower ∧ (cell12742 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12742 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12742 ⟨28,by decide⟩).lower ∧ (cell12742 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12742 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12742 ⟨29,by decide⟩).lower ∧ (cell12742 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12742 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12742 ⟨30,by decide⟩).lower ∧ (cell12742 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12742 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12742 ⟨31,by decide⟩).lower ∧ (cell12742 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12742 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12742 ⟨32,by decide⟩).lower ∧ (cell12742 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12742 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12742 ⟨33,by decide⟩).lower ∧ (cell12742 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12742 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12742 ⟨34,by decide⟩).lower ∧ (cell12742 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12742 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12742 ⟨35,by decide⟩).lower ∧ (cell12742 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12742 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12742 ⟨36,by decide⟩).lower ∧ (cell12742 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12742 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12742 ⟨37,by decide⟩).lower ∧ (cell12742 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12742 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12742 ⟨38,by decide⟩).lower ∧ (cell12742 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12742 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12742 ⟨39,by decide⟩).lower ∧ (cell12742 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12742 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12742 ⟨40,by decide⟩).lower ∧ (cell12742 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12742 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12742 ⟨41,by decide⟩).lower ∧ (cell12742 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12742 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12742 ⟨42,by decide⟩).lower ∧ (cell12742 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12742 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12742 ⟨43,by decide⟩).lower ∧ (cell12742 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12742 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12742 ⟨44,by decide⟩).lower ∧ (cell12742 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12742 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12742 ⟨45,by decide⟩).lower ∧ (cell12742 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12742 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12742 ⟨46,by decide⟩).lower ∧ (cell12742 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12742 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12742 ⟨47,by decide⟩).lower ∧ (cell12742 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12742 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12742 ⟨48,by decide⟩).lower ∧ (cell12742 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12742 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12742 ⟨49,by decide⟩).lower ∧ (cell12742 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12742 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12742 ⟨50,by decide⟩).lower ∧ (cell12742 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12742 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12742 ⟨51,by decide⟩).lower ∧ (cell12742 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12742 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12742 ⟨52,by decide⟩).lower ∧ (cell12742 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12742 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12742 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12742 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12742,cell12742,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12742 i).lower ∧
    (cell12742 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12742 i).upper ≤ (0.532 : ℝ) ∧
    (cell12742 i).centre ≤ (0.1 : ℝ) ∧ (cell12742 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12742 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12742 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12742

/-! The local source numeric instances at 12742 have no network premises. -/
namespace BstLean.Part269.N12742
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12742)
open BstLean.Part268 (cell12742)

noncomputable def sourceNumerics12742 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12742 (cell12742 i)
      scalarRow12742.M scalarRow12742.H scalarRow12742.xi := by
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
    energy_allowance := scalarRow12742.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12742]
    centre_nonneg := (scalarRow12742.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12742])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12742
/-! Actual 12743 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12743 ≤ (1.035748221653 : ℝ) := by
  have hr : (112.884897129775 : ℝ) ≤ √(12743 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.884897129775 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12743 12743 (11 / 1000) ≤
    (0.008467802523 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12743) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.884897129775 : ℝ) ≤ √(12743 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12743)
  have hdiv : K / √(12743 : ℝ) ≤ K / 112.884897129775 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.884897129775 ≤ (0.008467802523 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12743.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12743 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12743 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12743 := gPlus_lower 12743
end BstLean.Part269.N12743

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12743
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035748221652 : ℝ) ≤ wn 12743 := by
  have hn : √(12743 : ℝ) ≤ 112.884897129776 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12743 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.884897129776 ≤ 2 / √(12743 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251016138 : ℝ) ≤ rhoBar 12743 BstLean.Part154.csC ∧
    rhoBar 12743 BstLean.Part154.csC ≤ 0.000251016527 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035748221652 : ℝ) / (1.295212 * 12743) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035748221653 : ℝ) / (1.29521 * 12743) := by gcongr
      _ ≤ (0.000251016527 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12743 BstLean.Part154.csC) ≤ 0.001004129118 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12743 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) ≤ 0.000191728086 ∧
    cc1 (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) ≤ 0.000121997861 ∧
    cc2 (rhoBar 12743 BstLean.Part154.csC) ≤ 0.000070820700 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12743 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12743 BstLean.Part154.csC * nuR (rhoBar 12743 BstLean.Part154.csC)) ≤ 0.000502048807 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251016527 : ℝ) * 0.001004129118 := by gcongr
      _ ≤ (0.000502048807 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12743 BstLean.Part154.csC) * nuR (rhoBar 12743 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004129118 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12743 BstLean.Part154.csC) * rhoBar 12743 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251016527 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251016527 / 2 + 0.399 * 0.001004129118 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191728086 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502048807 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121997861 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251016527 / 1.414213562 := by gcongr
      _ ≤ (0.000070820700 : ℝ) := by norm_num

end BstLean.Part269.N12743

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12743
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) ≤ 1.58748E-7 := by
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12743 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12743 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191728086 : ℝ) ^ 2 + 0.000121997861 ^ 2 + 3 * 0.000070820700 ^ 2 +
        2 * 0.797885 * 0.000191728086 * 0.000121997861 + 2 * 0.000191728086 * 0.000070820700 +
        4 * 0.797885 * 0.000121997861 * 0.000070820700 := by gcongr
    _ ≤ (1.58748E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12743 BstLean.Part154.csC Θ ≤ 0.002620117735 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12743 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12743 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035748221653 * 1.58748E-7 / (0.000251016138 : ℝ) := by gcongr
    _ ≤ 0.002620117735 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12743 BstLean.Part154.csC Θ ≤ 0.002906979472 + 0.000662059037 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12743 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035748221653 : ℝ) * ((2 * Θ * 0.000251016527 +
        (6863 / 10000) * 0.000251016527 * 12743 * 0.001004129118) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002906979472 + 0.000662059037 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12743 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12743 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12743 0.011 Θ ∧ gammaRatio 12743 0.011 Θ ≤ 0.000086292991 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12743 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035748221653 : ℝ) * 0.525 / ((1 - 0.011) * 12743) := by gcongr
      _ ≤ (0.000086292991 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12743 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12743 0.011 Θ) :=
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
    badAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12743 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12743 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12743 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12743 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12743 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12743 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12743 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12743 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12743 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12743 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035748221653 : ℝ) * 12743 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003466063703 + 0.003282176772 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12743

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12743
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12743 BstLean.Part154.csC) (piBar (rhoBar 12743 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12743 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12743 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12743 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12743 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12743 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12743 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12743 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12743 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12743 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052394727000 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12743) ≤ 0.010579250294 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12743 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035748221653)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010579250294 + 2 * 0.737676 / 12743) := by gcongr
    _ ≤ (0.052394727000 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12743 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12743

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12743
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505506317 : ℝ) ≤ plow 12743 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12743) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695806509)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375561811) : eMP 12743 0.011 xi bn ≤ 0.001184281803 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12743 : ℝ) * (1 - 0.011))) ≤ 0.000585572979 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375561811 / (12743 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585572979 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585572979 : ℝ) + 3.141593 * 0.052695806509 / (12743 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184281803 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695806509)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375561811) : PiBarMP 12743 12 0.011 xi bn ≤ 0.160975904964 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12743 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037088567120 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.262313355818 : ℝ) ≤ √((12743 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.884897129775 : ℝ) ≤ √(12743 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12743) ≤ 0.123421366516 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037088567120 + 0.052695806509 * 1.772454 / (2 * (112.262313355818 : ℝ))) * (1 + 0.001184281803) +
        8 / (12743 * 112.884897129775) + 0.123421366516 := by gcongr
    _ ≤ (0.160975904964 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695806509)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375561811) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281950398917) :
    parallelOracle 12743 0.011 xi bn cd ≤ 0.161962771597 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12743 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12743 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505506317 : ℝ) ≤ plow 12743 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.884897129775 : ℝ) ≤ √(12743 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281950398917 : ℝ) / (2 * 0.560505506317 * 112.884897129775)) * 0.160975904964 +
        0.281950398917 ^ 2 / (2 * 0.560505506317 * 112.884897129775) := by gcongr
    _ ≤ (0.161962771597 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695806509) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375561811)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281950398917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12743 12743 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505506317 : ℝ) ≤ plow 12743 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.884897129775 : ℝ) ≤ √(12743 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12743 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12743 Θ 1.22 ≤ 0.011747368636 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.884897129775 := by gcongr <;> linarith
      _ ≤ (0.011747368636 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12743 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12743 12743 0.011 ≤ 0.008467802523 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12743 12743 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12743 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12743 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12743 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12743 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161962771597 + 0.011747368636 + (0.008467802523 : ℝ) *
        (1 + 2 * (0.281950398917 + 0.011747368636) / (0.560505506317 * 112.884897129775))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12743]

end BstLean.Part269.N12743

/-! The original eight local profiles supply actual 12743 moment certificates. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12743 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052695806509 ∧
    0 ≤ bN 12743 BstLean.Part154.csC (groupTheta g) ∧ bN 12743 BstLean.Part154.csC (groupTheta g) ≤ 0.001375561811 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12743 12743 0.011
      (momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12743 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12743 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12743 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229555671917 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12743 0.011
      (momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12743 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12743
/-! The actual computed-centre upper energy formula at 12743. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12743

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12743)
open BstLean.Part268 (cell12743)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085365843301
  | 2 => 0.086306329065
  | 3 => 0.087244627853
  | 4 => 0.088182082235
  | 5 => 0.089120318570
  | 6 => 0.090061289479
  | 7 => 0.091007320362
  | 8 => 0.091961160031
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12743 12743 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12743 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12743

/-! Actual upper energy certificates on all 43 source endpoints at 12743. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12743)
open BstLean.Part268 (cell12743)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12743 (gMinus 12743) (1 - (cell12743 i).lower) ≤ 1 ∧
    energyUpper 12743 (gMinus 12743) (BstLean.Part211.gPlus 12743)
      (finiteEnergy 12743 12743 0.011) (1 - (cell12743 i).lower) ≤
      (cell12743 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨10,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨11,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨12,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨13,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨14,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨15,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨16,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨17,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨18,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨19,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨20,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨21,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨22,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨23,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨24,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨25,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨26,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨27,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨28,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨29,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨30,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨31,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨32,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨33,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨34,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨35,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨36,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨37,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨38,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨39,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨40,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨41,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨42,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨43,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨44,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨45,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨46,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨47,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨48,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨49,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨50,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨51,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12743) (by norm_num)
        (q := 1 - (cell12743 ⟨52,by decide⟩).lower)
        (by norm_num [cell12743]) (by norm_num [cell12743])
      exact ⟨E.1,E.2.trans (by norm_num [cell12743])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12743

/-! Source-cell containment and simple scalar guards at 12743. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12743)
open BstLean.Part268 (cell12743)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12743 ⟨10,by decide⟩).lower ∧ (cell12743 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12743 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12743 ⟨11,by decide⟩).lower ∧ (cell12743 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12743 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12743 ⟨12,by decide⟩).lower ∧ (cell12743 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12743 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12743 ⟨13,by decide⟩).lower ∧ (cell12743 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12743 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12743 ⟨14,by decide⟩).lower ∧ (cell12743 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12743 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12743 ⟨15,by decide⟩).lower ∧ (cell12743 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12743 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12743 ⟨16,by decide⟩).lower ∧ (cell12743 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12743 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12743 ⟨17,by decide⟩).lower ∧ (cell12743 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12743 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12743 ⟨18,by decide⟩).lower ∧ (cell12743 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12743 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12743 ⟨19,by decide⟩).lower ∧ (cell12743 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12743 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12743 ⟨20,by decide⟩).lower ∧ (cell12743 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12743 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12743 ⟨21,by decide⟩).lower ∧ (cell12743 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12743 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12743 ⟨22,by decide⟩).lower ∧ (cell12743 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12743 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12743 ⟨23,by decide⟩).lower ∧ (cell12743 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12743 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12743 ⟨24,by decide⟩).lower ∧ (cell12743 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12743 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12743 ⟨25,by decide⟩).lower ∧ (cell12743 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12743 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12743 ⟨26,by decide⟩).lower ∧ (cell12743 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12743 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12743 ⟨27,by decide⟩).lower ∧ (cell12743 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12743 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12743 ⟨28,by decide⟩).lower ∧ (cell12743 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12743 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12743 ⟨29,by decide⟩).lower ∧ (cell12743 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12743 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12743 ⟨30,by decide⟩).lower ∧ (cell12743 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12743 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12743 ⟨31,by decide⟩).lower ∧ (cell12743 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12743 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12743 ⟨32,by decide⟩).lower ∧ (cell12743 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12743 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12743 ⟨33,by decide⟩).lower ∧ (cell12743 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12743 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12743 ⟨34,by decide⟩).lower ∧ (cell12743 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12743 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12743 ⟨35,by decide⟩).lower ∧ (cell12743 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12743 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12743 ⟨36,by decide⟩).lower ∧ (cell12743 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12743 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12743 ⟨37,by decide⟩).lower ∧ (cell12743 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12743 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12743 ⟨38,by decide⟩).lower ∧ (cell12743 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12743 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12743 ⟨39,by decide⟩).lower ∧ (cell12743 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12743 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12743 ⟨40,by decide⟩).lower ∧ (cell12743 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12743 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12743 ⟨41,by decide⟩).lower ∧ (cell12743 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12743 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12743 ⟨42,by decide⟩).lower ∧ (cell12743 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12743 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12743 ⟨43,by decide⟩).lower ∧ (cell12743 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12743 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12743 ⟨44,by decide⟩).lower ∧ (cell12743 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12743 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12743 ⟨45,by decide⟩).lower ∧ (cell12743 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12743 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12743 ⟨46,by decide⟩).lower ∧ (cell12743 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12743 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12743 ⟨47,by decide⟩).lower ∧ (cell12743 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12743 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12743 ⟨48,by decide⟩).lower ∧ (cell12743 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12743 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12743 ⟨49,by decide⟩).lower ∧ (cell12743 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12743 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12743 ⟨50,by decide⟩).lower ∧ (cell12743 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12743 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12743 ⟨51,by decide⟩).lower ∧ (cell12743 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12743 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12743 ⟨52,by decide⟩).lower ∧ (cell12743 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12743 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12743 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12743 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12743,cell12743,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12743 i).lower ∧
    (cell12743 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12743 i).upper ≤ (0.532 : ℝ) ∧
    (cell12743 i).centre ≤ (0.1 : ℝ) ∧ (cell12743 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12743 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12743 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12743

/-! The local source numeric instances at 12743 have no network premises. -/
namespace BstLean.Part269.N12743
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12743)
open BstLean.Part268 (cell12743)

noncomputable def sourceNumerics12743 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12743 (cell12743 i)
      scalarRow12743.M scalarRow12743.H scalarRow12743.xi := by
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
    energy_allowance := scalarRow12743.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12743]
    centre_nonneg := (scalarRow12743.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12743])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12743
/-! Actual 12744 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12744 ≤ (1.035746806759 : ℝ) := by
  have hr : (112.889326333360 : ℝ) ≤ √(12744 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.889326333360 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12744 12744 (11 / 1000) ≤
    (0.008467470287 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12744) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.889326333360 : ℝ) ≤ √(12744 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12744)
  have hdiv : K / √(12744 : ℝ) ≤ K / 112.889326333360 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.889326333360 ≤ (0.008467470287 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12744.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12744 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12744 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12744 := gPlus_lower 12744
end BstLean.Part269.N12744

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12744
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035746806758 : ℝ) ≤ wn 12744 := by
  have hn : √(12744 : ℝ) ≤ 112.889326333361 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12744 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.889326333361 ≤ 2 / √(12744 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250996099 : ℝ) ≤ rhoBar 12744 BstLean.Part154.csC ∧
    rhoBar 12744 BstLean.Part154.csC ≤ 0.000250996487 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035746806758 : ℝ) / (1.295212 * 12744) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035746806759 : ℝ) / (1.29521 * 12744) := by gcongr
      _ ≤ (0.000250996487 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12744 BstLean.Part154.csC) ≤ 0.001004048948 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12744 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) ≤ 0.000191712779 ∧
    cc1 (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) ≤ 0.000121988120 ∧
    cc2 (rhoBar 12744 BstLean.Part154.csC) ≤ 0.000070815046 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12744 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12744 BstLean.Part154.csC * nuR (rhoBar 12744 BstLean.Part154.csC)) ≤ 0.000502008724 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250996487 : ℝ) * 0.001004048948 := by gcongr
      _ ≤ (0.000502008724 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12744 BstLean.Part154.csC) * nuR (rhoBar 12744 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001004048948 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12744 BstLean.Part154.csC) * rhoBar 12744 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250996487 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250996487 / 2 + 0.399 * 0.001004048948 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191712779 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000502008724 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121988120 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250996487 / 1.414213562 := by gcongr
      _ ≤ (0.000070815046 : ℝ) := by norm_num

end BstLean.Part269.N12744

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12744
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) ≤ 1.58722E-7 := by
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12744 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12744 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191712779 : ℝ) ^ 2 + 0.000121988120 ^ 2 + 3 * 0.000070815046 ^ 2 +
        2 * 0.797885 * 0.000191712779 * 0.000121988120 + 2 * 0.000191712779 * 0.000070815046 +
        4 * 0.797885 * 0.000121988120 * 0.000070815046 := by gcongr
    _ ≤ (1.58722E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12744 BstLean.Part154.csC Θ ≤ 0.002619894179 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12744 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12744 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035746806759 * 1.58722E-7 / (0.000250996099 : ℝ) := by gcongr
    _ ≤ 0.002619894179 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12744 BstLean.Part154.csC Θ ≤ 0.002906739433 + 0.000662005277 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12744 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035746806759 : ℝ) * ((2 * Θ * 0.000250996487 +
        (6863 / 10000) * 0.000250996487 * 12744 * 0.001004048948) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002906739433 + 0.000662005277 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12744 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12744 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12744 0.011 Θ ∧ gammaRatio 12744 0.011 Θ ≤ 0.000086286102 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12744 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035746806759 : ℝ) * 0.525 / ((1 - 0.011) * 12744) := by gcongr
      _ ≤ (0.000086286102 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12744 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12744 0.011 Θ) :=
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
    badAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12744 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12744 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12744 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12744 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12744 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12744 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12744 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12744 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12744 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12744 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035746806759 : ℝ) * 12744 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465823664 + 0.003281899456 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12744

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12744
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12744 BstLean.Part154.csC) (piBar (rhoBar 12744 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12744 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12744 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12744 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12744 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12744 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12744 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12744 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12744 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12744 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052392649045 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12744) ≤ 0.010578835218 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12744 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035746806759)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010578835218 + 2 * 0.737676 / 12744) := by gcongr
    _ ≤ (0.052392649045 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12744 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12744

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12744
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505551231 : ℝ) ≤ plow 12744 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12744) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695420879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375444444) : eMP 12744 0.011 xi bn ≤ 0.001184184764 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12744 : ℝ) * (1 - 0.011))) ≤ 0.000585525023 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375444444 / (12744 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585525023 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585525023 : ℝ) + 3.141593 * 0.052695420879 / (12744 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184184764 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695420879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375444444) : PiBarMP 12744 12 0.011 xi bn ≤ 0.160969454694 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12744 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037086984833 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.266718131421 : ℝ) ≤ √((12744 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.889326333360 : ℝ) ≤ √(12744 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12744) ≤ 0.123416524089 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037086984833 + 0.052695420879 * 1.772454 / (2 * (112.266718131421 : ℝ))) * (1 + 0.001184184764) +
        8 / (12744 * 112.889326333360) + 0.123416524089 := by gcongr
    _ ≤ (0.160969454694 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695420879)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375444444) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281947481012) :
    parallelOracle 12744 0.011 xi bn cd ≤ 0.161956251444 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12744 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12744 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505551231 : ℝ) ≤ plow 12744 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.889326333360 : ℝ) ≤ √(12744 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281947481012 : ℝ) / (2 * 0.560505551231 * 112.889326333360)) * 0.160969454694 +
        0.281947481012 ^ 2 / (2 * 0.560505551231 * 112.889326333360) := by gcongr
    _ ≤ (0.161956251444 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695420879) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375444444)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281947481012) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12744 12744 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505551231 : ℝ) ≤ plow 12744 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.889326333360 : ℝ) ≤ √(12744 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12744 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12744 Θ 1.22 ≤ 0.011746907729 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.889326333360 := by gcongr <;> linarith
      _ ≤ (0.011746907729 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12744 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12744 12744 0.011 ≤ 0.008467470287 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12744 12744 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12744 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12744 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12744 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12744 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161956251444 + 0.011746907729 + (0.008467470287 : ℝ) *
        (1 + 2 * (0.281947481012 + 0.011746907729) / (0.560505551231 * 112.889326333360))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12744]

end BstLean.Part269.N12744

/-! The original eight local profiles supply actual 12744 moment certificates. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12744 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052695420879 ∧
    0 ≤ bN 12744 BstLean.Part154.csC (groupTheta g) ∧ bN 12744 BstLean.Part154.csC (groupTheta g) ≤ 0.001375444444 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12744 12744 0.011
      (momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12744 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12744 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12744 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229554831967 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12744 0.011
      (momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12744 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12744
/-! The actual computed-centre upper energy formula at 12744. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12744

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12744)
open BstLean.Part268 (cell12744)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085362973138
  | 2 => 0.086303407205
  | 3 => 0.087241646923
  | 4 => 0.088179033150
  | 5 => 0.089117190232
  | 6 => 0.090058068432
  | 7 => 0.091003990413
  | 8 => 0.091957701822
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12744 12744 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12744 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12744

/-! Actual upper energy certificates on all 43 source endpoints at 12744. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12744)
open BstLean.Part268 (cell12744)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12744 (gMinus 12744) (1 - (cell12744 i).lower) ≤ 1 ∧
    energyUpper 12744 (gMinus 12744) (BstLean.Part211.gPlus 12744)
      (finiteEnergy 12744 12744 0.011) (1 - (cell12744 i).lower) ≤
      (cell12744 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨10,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨11,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨12,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨13,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨14,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨15,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨16,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨17,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨18,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨19,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨20,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨21,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨22,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨23,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨24,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨25,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨26,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨27,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨28,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨29,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨30,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨31,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨32,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨33,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨34,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨35,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨36,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨37,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨38,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨39,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨40,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨41,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨42,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨43,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨44,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨45,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨46,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨47,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨48,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨49,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨50,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨51,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12744) (by norm_num)
        (q := 1 - (cell12744 ⟨52,by decide⟩).lower)
        (by norm_num [cell12744]) (by norm_num [cell12744])
      exact ⟨E.1,E.2.trans (by norm_num [cell12744])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12744

/-! Source-cell containment and simple scalar guards at 12744. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12744)
open BstLean.Part268 (cell12744)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12744 ⟨10,by decide⟩).lower ∧ (cell12744 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12744 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12744 ⟨11,by decide⟩).lower ∧ (cell12744 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12744 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12744 ⟨12,by decide⟩).lower ∧ (cell12744 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12744 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12744 ⟨13,by decide⟩).lower ∧ (cell12744 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12744 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12744 ⟨14,by decide⟩).lower ∧ (cell12744 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12744 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12744 ⟨15,by decide⟩).lower ∧ (cell12744 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12744 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12744 ⟨16,by decide⟩).lower ∧ (cell12744 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12744 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12744 ⟨17,by decide⟩).lower ∧ (cell12744 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12744 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12744 ⟨18,by decide⟩).lower ∧ (cell12744 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12744 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12744 ⟨19,by decide⟩).lower ∧ (cell12744 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12744 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12744 ⟨20,by decide⟩).lower ∧ (cell12744 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12744 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12744 ⟨21,by decide⟩).lower ∧ (cell12744 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12744 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12744 ⟨22,by decide⟩).lower ∧ (cell12744 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12744 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12744 ⟨23,by decide⟩).lower ∧ (cell12744 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12744 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12744 ⟨24,by decide⟩).lower ∧ (cell12744 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12744 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12744 ⟨25,by decide⟩).lower ∧ (cell12744 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12744 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12744 ⟨26,by decide⟩).lower ∧ (cell12744 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12744 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12744 ⟨27,by decide⟩).lower ∧ (cell12744 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12744 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12744 ⟨28,by decide⟩).lower ∧ (cell12744 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12744 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12744 ⟨29,by decide⟩).lower ∧ (cell12744 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12744 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12744 ⟨30,by decide⟩).lower ∧ (cell12744 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12744 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12744 ⟨31,by decide⟩).lower ∧ (cell12744 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12744 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12744 ⟨32,by decide⟩).lower ∧ (cell12744 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12744 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12744 ⟨33,by decide⟩).lower ∧ (cell12744 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12744 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12744 ⟨34,by decide⟩).lower ∧ (cell12744 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12744 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12744 ⟨35,by decide⟩).lower ∧ (cell12744 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12744 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12744 ⟨36,by decide⟩).lower ∧ (cell12744 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12744 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12744 ⟨37,by decide⟩).lower ∧ (cell12744 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12744 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12744 ⟨38,by decide⟩).lower ∧ (cell12744 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12744 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12744 ⟨39,by decide⟩).lower ∧ (cell12744 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12744 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12744 ⟨40,by decide⟩).lower ∧ (cell12744 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12744 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12744 ⟨41,by decide⟩).lower ∧ (cell12744 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12744 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12744 ⟨42,by decide⟩).lower ∧ (cell12744 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12744 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12744 ⟨43,by decide⟩).lower ∧ (cell12744 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12744 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12744 ⟨44,by decide⟩).lower ∧ (cell12744 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12744 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12744 ⟨45,by decide⟩).lower ∧ (cell12744 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12744 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12744 ⟨46,by decide⟩).lower ∧ (cell12744 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12744 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12744 ⟨47,by decide⟩).lower ∧ (cell12744 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12744 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12744 ⟨48,by decide⟩).lower ∧ (cell12744 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12744 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12744 ⟨49,by decide⟩).lower ∧ (cell12744 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12744 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12744 ⟨50,by decide⟩).lower ∧ (cell12744 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12744 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12744 ⟨51,by decide⟩).lower ∧ (cell12744 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12744 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12744 ⟨52,by decide⟩).lower ∧ (cell12744 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12744 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12744 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12744 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12744,cell12744,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12744 i).lower ∧
    (cell12744 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12744 i).upper ≤ (0.532 : ℝ) ∧
    (cell12744 i).centre ≤ (0.1 : ℝ) ∧ (cell12744 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12744 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12744 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12744

/-! The local source numeric instances at 12744 have no network premises. -/
namespace BstLean.Part269.N12744
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12744)
open BstLean.Part268 (cell12744)

noncomputable def sourceNumerics12744 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12744 (cell12744 i)
      scalarRow12744.M scalarRow12744.H scalarRow12744.xi := by
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
    energy_allowance := scalarRow12744.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12744]
    centre_nonneg := (scalarRow12744.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12744])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12744
/-! Actual 12745 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12745 ≤ (1.035745392033 : ℝ) := by
  have hr : (112.893755363173 : ℝ) ≤ √(12745 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.893755363173 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12745 12745 (11 / 1000) ≤
    (0.008467138090 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12745) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.893755363173 : ℝ) ≤ √(12745 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12745)
  have hdiv : K / √(12745 : ℝ) ≤ K / 112.893755363173 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.893755363173 ≤ (0.008467138090 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12745.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12745 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12745 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12745 := gPlus_lower 12745
end BstLean.Part269.N12745

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12745
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035745392032 : ℝ) ≤ wn 12745 := by
  have hn : √(12745 : ℝ) ≤ 112.893755363174 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12745 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.893755363174 ≤ 2 / √(12745 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250976062 : ℝ) ≤ rhoBar 12745 BstLean.Part154.csC ∧
    rhoBar 12745 BstLean.Part154.csC ≤ 0.000250976451 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035745392032 : ℝ) / (1.295212 * 12745) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035745392033 : ℝ) / (1.29521 * 12745) := by gcongr
      _ ≤ (0.000250976451 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12745 BstLean.Part154.csC) ≤ 0.001003968794 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12745 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) ≤ 0.000191697474 ∧
    cc1 (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) ≤ 0.000121978382 ∧
    cc2 (rhoBar 12745 BstLean.Part154.csC) ≤ 0.000070809394 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12745 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12745 BstLean.Part154.csC * nuR (rhoBar 12745 BstLean.Part154.csC)) ≤ 0.000501968650 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250976451 : ℝ) * 0.001003968794 := by gcongr
      _ ≤ (0.000501968650 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12745 BstLean.Part154.csC) * nuR (rhoBar 12745 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003968794 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12745 BstLean.Part154.csC) * rhoBar 12745 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250976451 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250976451 / 2 + 0.399 * 0.001003968794 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191697474 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501968650 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121978382 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250976451 / 1.414213562 := by gcongr
      _ ≤ (0.000070809394 : ℝ) := by norm_num

end BstLean.Part269.N12745

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12745
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) ≤ 1.58697E-7 := by
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12745 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12745 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191697474 : ℝ) ^ 2 + 0.000121978382 ^ 2 + 3 * 0.000070809394 ^ 2 +
        2 * 0.797885 * 0.000191697474 * 0.000121978382 + 2 * 0.000191697474 * 0.000070809394 +
        4 * 0.797885 * 0.000121978382 * 0.000070809394 := by gcongr
    _ ≤ (1.58697E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12745 BstLean.Part154.csC Θ ≤ 0.002619687076 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12745 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12745 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035745392033 * 1.58697E-7 / (0.000250976062 : ℝ) := by gcongr
    _ ≤ 0.002619687076 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12745 BstLean.Part154.csC Θ ≤ 0.002906499451 + 0.000661951527 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12745 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035745392033 : ℝ) * ((2 * Θ * 0.000250976451 +
        (6863 / 10000) * 0.000250976451 * 12745 * 0.001003968794) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002906499451 + 0.000661951527 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12745 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12745 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12745 0.011 Θ ∧ gammaRatio 12745 0.011 Θ ≤ 0.000086279214 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12745 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035745392033 : ℝ) * 0.525 / ((1 - 0.011) * 12745) := by gcongr
      _ ≤ (0.000086279214 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12745 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12745 0.011 Θ) :=
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
    badAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12745 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12745 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12745 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12745 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12745 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12745 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12745 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12745 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12745 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12745 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035745392033 : ℝ) * 12745 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465583682 + 0.003281638603 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12745

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12745
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12745 BstLean.Part154.csC) (piBar (rhoBar 12745 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12745 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12745 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12745 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12745 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12745 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12745 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12745 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12745 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12745 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052390571331 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12745) ≤ 0.010578420190 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12745 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035745392033)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010578420190 + 2 * 0.737676 / 12745) := by gcongr
    _ ≤ (0.052390571331 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12745 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12745

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12745
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505596139 : ℝ) ≤ plow 12745 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12745) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695043949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375335715) : eMP 12745 0.011 xi bn ≤ 0.001184091414 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12745 : ℝ) * (1 - 0.011))) ≤ 0.000585478910 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375335715 / (12745 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585478910 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585478910 : ℝ) + 3.141593 * 0.052695043949 / (12745 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001184091414 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695043949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375335715) : PiBarMP 12745 12 0.011 xi bn ≤ 0.160963121735 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12745 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037085518940 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.271122734209 : ℝ) ≤ √((12745 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.893755363173 : ℝ) ≤ √(12745 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12745) ≤ 0.123411682232 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037085518940 + 0.052695043949 * 1.772454 / (2 * (112.271122734209 : ℝ))) * (1 + 0.001184091414) +
        8 / (12745 * 112.893755363173) + 0.123411682232 := by gcongr
    _ ≤ (0.160963121735 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695043949)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375335715) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281944582294) :
    parallelOracle 12745 0.011 xi bn cd ≤ 0.161949848980 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12745 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12745 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505596139 : ℝ) ≤ plow 12745 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.893755363173 : ℝ) ≤ √(12745 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281944582294 : ℝ) / (2 * 0.560505596139 * 112.893755363173)) * 0.160963121735 +
        0.281944582294 ^ 2 / (2 * 0.560505596139 * 112.893755363173) := by gcongr
    _ ≤ (0.161949848980 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052695043949) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375335715)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281944582294) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12745 12745 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505596139 : ℝ) ≤ plow 12745 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.893755363173 : ℝ) ≤ √(12745 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12745 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12745 Θ 1.22 ≤ 0.011746446876 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.893755363173 := by gcongr <;> linarith
      _ ≤ (0.011746446876 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12745 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12745 12745 0.011 ≤ 0.008467138090 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12745 12745 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12745 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12745 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12745 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12745 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161949848980 + 0.011746446876 + (0.008467138090 : ℝ) *
        (1 + 2 * (0.281944582294 + 0.011746446876) / (0.560505596139 * 112.893755363173))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12745]

end BstLean.Part269.N12745

/-! The original eight local profiles supply actual 12745 moment certificates. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12745 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052695043949 ∧
    0 ≤ bN 12745 BstLean.Part154.csC (groupTheta g) ∧ bN 12745 BstLean.Part154.csC (groupTheta g) ≤ 0.001375335715 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12745 12745 0.011
      (momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12745 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12745 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12745 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229554010963 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12745 0.011
      (momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12745 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12745
/-! The actual computed-centre upper energy formula at 12745. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12745

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12745)
open BstLean.Part268 (cell12745)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085360104012
  | 2 => 0.086300486425
  | 3 => 0.087238667124
  | 4 => 0.088175985260
  | 5 => 0.089114063167
  | 6 => 0.090054848754
  | 7 => 0.091000661947
  | 8 => 0.091954245235
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12745 12745 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12745 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12745

/-! Actual upper energy certificates on all 43 source endpoints at 12745. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12745)
open BstLean.Part268 (cell12745)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12745 (gMinus 12745) (1 - (cell12745 i).lower) ≤ 1 ∧
    energyUpper 12745 (gMinus 12745) (BstLean.Part211.gPlus 12745)
      (finiteEnergy 12745 12745 0.011) (1 - (cell12745 i).lower) ≤
      (cell12745 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨10,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨11,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨12,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨13,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨14,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨15,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨16,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨17,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨18,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨19,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨20,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨21,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨22,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨23,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨24,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨25,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨26,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨27,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨28,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨29,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨30,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨31,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨32,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨33,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨34,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨35,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨36,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨37,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨38,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨39,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨40,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨41,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨42,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨43,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨44,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨45,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨46,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨47,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨48,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨49,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨50,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨51,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12745) (by norm_num)
        (q := 1 - (cell12745 ⟨52,by decide⟩).lower)
        (by norm_num [cell12745]) (by norm_num [cell12745])
      exact ⟨E.1,E.2.trans (by norm_num [cell12745])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12745

/-! Source-cell containment and simple scalar guards at 12745. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12745)
open BstLean.Part268 (cell12745)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12745 ⟨10,by decide⟩).lower ∧ (cell12745 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12745 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12745 ⟨11,by decide⟩).lower ∧ (cell12745 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12745 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12745 ⟨12,by decide⟩).lower ∧ (cell12745 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12745 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12745 ⟨13,by decide⟩).lower ∧ (cell12745 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12745 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12745 ⟨14,by decide⟩).lower ∧ (cell12745 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12745 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12745 ⟨15,by decide⟩).lower ∧ (cell12745 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12745 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12745 ⟨16,by decide⟩).lower ∧ (cell12745 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12745 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12745 ⟨17,by decide⟩).lower ∧ (cell12745 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12745 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12745 ⟨18,by decide⟩).lower ∧ (cell12745 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12745 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12745 ⟨19,by decide⟩).lower ∧ (cell12745 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12745 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12745 ⟨20,by decide⟩).lower ∧ (cell12745 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12745 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12745 ⟨21,by decide⟩).lower ∧ (cell12745 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12745 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12745 ⟨22,by decide⟩).lower ∧ (cell12745 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12745 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12745 ⟨23,by decide⟩).lower ∧ (cell12745 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12745 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12745 ⟨24,by decide⟩).lower ∧ (cell12745 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12745 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12745 ⟨25,by decide⟩).lower ∧ (cell12745 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12745 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12745 ⟨26,by decide⟩).lower ∧ (cell12745 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12745 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12745 ⟨27,by decide⟩).lower ∧ (cell12745 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12745 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12745 ⟨28,by decide⟩).lower ∧ (cell12745 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12745 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12745 ⟨29,by decide⟩).lower ∧ (cell12745 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12745 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12745 ⟨30,by decide⟩).lower ∧ (cell12745 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12745 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12745 ⟨31,by decide⟩).lower ∧ (cell12745 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12745 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12745 ⟨32,by decide⟩).lower ∧ (cell12745 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12745 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12745 ⟨33,by decide⟩).lower ∧ (cell12745 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12745 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12745 ⟨34,by decide⟩).lower ∧ (cell12745 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12745 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12745 ⟨35,by decide⟩).lower ∧ (cell12745 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12745 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12745 ⟨36,by decide⟩).lower ∧ (cell12745 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12745 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12745 ⟨37,by decide⟩).lower ∧ (cell12745 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12745 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12745 ⟨38,by decide⟩).lower ∧ (cell12745 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12745 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12745 ⟨39,by decide⟩).lower ∧ (cell12745 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12745 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12745 ⟨40,by decide⟩).lower ∧ (cell12745 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12745 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12745 ⟨41,by decide⟩).lower ∧ (cell12745 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12745 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12745 ⟨42,by decide⟩).lower ∧ (cell12745 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12745 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12745 ⟨43,by decide⟩).lower ∧ (cell12745 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12745 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12745 ⟨44,by decide⟩).lower ∧ (cell12745 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12745 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12745 ⟨45,by decide⟩).lower ∧ (cell12745 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12745 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12745 ⟨46,by decide⟩).lower ∧ (cell12745 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12745 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12745 ⟨47,by decide⟩).lower ∧ (cell12745 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12745 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12745 ⟨48,by decide⟩).lower ∧ (cell12745 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12745 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12745 ⟨49,by decide⟩).lower ∧ (cell12745 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12745 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12745 ⟨50,by decide⟩).lower ∧ (cell12745 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12745 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12745 ⟨51,by decide⟩).lower ∧ (cell12745 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12745 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12745 ⟨52,by decide⟩).lower ∧ (cell12745 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12745 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12745 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12745 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12745,cell12745,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12745 i).lower ∧
    (cell12745 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12745 i).upper ≤ (0.532 : ℝ) ∧
    (cell12745 i).centre ≤ (0.1 : ℝ) ∧ (cell12745 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12745 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12745 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12745

/-! The local source numeric instances at 12745 have no network premises. -/
namespace BstLean.Part269.N12745
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12745)
open BstLean.Part268 (cell12745)

noncomputable def sourceNumerics12745 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12745 (cell12745 i)
      scalarRow12745.M scalarRow12745.H scalarRow12745.xi := by
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
    energy_allowance := scalarRow12745.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12745]
    centre_nonneg := (scalarRow12745.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12745])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12745
/-! Actual 12746 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12746 ≤ (1.035743977474 : ℝ) := by
  have hr : (112.898184219233 : ℝ) ≤ √(12746 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.898184219233 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12746 12746 (11 / 1000) ≤
    (0.008466805932 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12746) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.898184219233 : ℝ) ≤ √(12746 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12746)
  have hdiv : K / √(12746 : ℝ) ≤ K / 112.898184219233 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.898184219233 ≤ (0.008466805932 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12746.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12746 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12746 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12746 := gPlus_lower 12746
end BstLean.Part269.N12746

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12746
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035743977473 : ℝ) ≤ wn 12746 := by
  have hn : √(12746 : ℝ) ≤ 112.898184219234 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12746 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.898184219234 ≤ 2 / √(12746 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250956029 : ℝ) ≤ rhoBar 12746 BstLean.Part154.csC ∧
    rhoBar 12746 BstLean.Part154.csC ≤ 0.000250956417 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035743977473 : ℝ) / (1.295212 * 12746) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035743977474 : ℝ) / (1.29521 * 12746) := by gcongr
      _ ≤ (0.000250956417 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12746 BstLean.Part154.csC) ≤ 0.001003888648 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12746 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) ≤ 0.000191682172 ∧
    cc1 (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) ≤ 0.000121968645 ∧
    cc2 (rhoBar 12746 BstLean.Part154.csC) ≤ 0.000070803741 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12746 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12746 BstLean.Part154.csC * nuR (rhoBar 12746 BstLean.Part154.csC)) ≤ 0.000501928579 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250956417 : ℝ) * 0.001003888648 := by gcongr
      _ ≤ (0.000501928579 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12746 BstLean.Part154.csC) * nuR (rhoBar 12746 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003888648 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12746 BstLean.Part154.csC) * rhoBar 12746 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250956417 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250956417 / 2 + 0.399 * 0.001003888648 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191682172 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501928579 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121968645 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250956417 / 1.414213562 := by gcongr
      _ ≤ (0.000070803741 : ℝ) := by norm_num

end BstLean.Part269.N12746

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12746
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) ≤ 1.58672E-7 := by
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12746 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12746 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191682172 : ℝ) ^ 2 + 0.000121968645 ^ 2 + 3 * 0.000070803741 ^ 2 +
        2 * 0.797885 * 0.000191682172 * 0.000121968645 + 2 * 0.000191682172 * 0.000070803741 +
        4 * 0.797885 * 0.000121968645 * 0.000070803741 := by gcongr
    _ ≤ (1.58672E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12746 BstLean.Part154.csC Θ ≤ 0.002619479900 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12746 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12746 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035743977474 * 1.58672E-7 / (0.000250956029 : ℝ) := by gcongr
    _ ≤ 0.002619479900 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12746 BstLean.Part154.csC Θ ≤ 0.002906259482 + 0.000661897784 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12746 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035743977474 : ℝ) * ((2 * Θ * 0.000250956417 +
        (6863 / 10000) * 0.000250956417 * 12746 * 0.001003888648) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002906259482 + 0.000661897784 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12746 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12746 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12746 0.011 Θ ∧ gammaRatio 12746 0.011 Θ ≤ 0.000086272327 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12746 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035743977474 : ℝ) * 0.525 / ((1 - 0.011) * 12746) := by gcongr
      _ ≤ (0.000086272327 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12746 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12746 0.011 Θ) :=
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
    badAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12746 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12746 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12746 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12746 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12746 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12746 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12746 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12746 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12746 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12746 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035743977474 : ℝ) * 12746 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465343713 + 0.003281377684 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12746

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12746
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12746 BstLean.Part154.csC) (piBar (rhoBar 12746 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12746 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12746 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12746 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12746 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12746 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12746 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12746 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12746 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12746 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052388493870 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12746) ≤ 0.010578005212 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12746 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035743977474)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010578005212 + 2 * 0.737676 / 12746) := by gcongr
    _ ≤ (0.052388493870 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12746 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12746

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12746
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505641040 : ℝ) ≤ plow 12746 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12746) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694666998)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375226948) : eMP 12746 0.011 xi bn ≤ 0.001183998053 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12746 : ℝ) * (1 - 0.011))) ≤ 0.000585432792 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375226948 / (12746 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585432792 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585432792 : ℝ) + 3.141593 * 0.052694666998 / (12746 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183998053 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694666998)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375226948) : PiBarMP 12746 12 0.011 xi bn ≤ 0.160956788776 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12746 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037084052476 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.275527164204 : ℝ) ≤ √((12746 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.898184219233 : ℝ) ≤ √(12746 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12746) ≤ 0.123406840944 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037084052476 + 0.052694666998 * 1.772454 / (2 * (112.275527164204 : ℝ))) * (1 + 0.001183998053) +
        8 / (12746 * 112.898184219233) + 0.123406840944 := by gcongr
    _ ≤ (0.160956788776 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694666998)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375226948) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281941683781) :
    parallelOracle 12746 0.011 xi bn cd ≤ 0.161943446525 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12746 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12746 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505641040 : ℝ) ≤ plow 12746 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.898184219233 : ℝ) ≤ √(12746 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281941683781 : ℝ) / (2 * 0.560505641040 * 112.898184219233)) * 0.160956788776 +
        0.281941683781 ^ 2 / (2 * 0.560505641040 * 112.898184219233) := by gcongr
    _ ≤ (0.161943446525 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694666998) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375226948)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281941683781) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12746 12746 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505641040 : ℝ) ≤ plow 12746 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.898184219233 : ℝ) ≤ √(12746 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12746 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12746 Θ 1.22 ≤ 0.011745986078 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.898184219233 := by gcongr <;> linarith
      _ ≤ (0.011745986078 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12746 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12746 12746 0.011 ≤ 0.008466805932 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12746 12746 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12746 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12746 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12746 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12746 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161943446525 + 0.011745986078 + (0.008466805932 : ℝ) *
        (1 + 2 * (0.281941683781 + 0.011745986078) / (0.560505641040 * 112.898184219233))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12746]

end BstLean.Part269.N12746

/-! The original eight local profiles supply actual 12746 moment certificates. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12746 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052694666998 ∧
    0 ≤ bN 12746 BstLean.Part154.csC (groupTheta g) ∧ bN 12746 BstLean.Part154.csC (groupTheta g) ≤ 0.001375226948 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12746 12746 0.011
      (momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12746 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12746 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12746 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229553189911 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12746 0.011
      (momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12746 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12746
/-! The actual computed-centre upper energy formula at 12746. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12746

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12746)
open BstLean.Part268 (cell12746)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085357235923
  | 2 => 0.086297566722
  | 3 => 0.087235688454
  | 4 => 0.088172938563
  | 5 => 0.089110937373
  | 6 => 0.090051630441
  | 7 => 0.090997334963
  | 8 => 0.091950790266
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12746 12746 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12746 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12746

/-! Actual upper energy certificates on all 43 source endpoints at 12746. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12746)
open BstLean.Part268 (cell12746)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12746 (gMinus 12746) (1 - (cell12746 i).lower) ≤ 1 ∧
    energyUpper 12746 (gMinus 12746) (BstLean.Part211.gPlus 12746)
      (finiteEnergy 12746 12746 0.011) (1 - (cell12746 i).lower) ≤
      (cell12746 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨10,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨11,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨12,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨13,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨14,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨15,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨16,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨17,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨18,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨19,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨20,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨21,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨22,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨23,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨24,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨25,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨26,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨27,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨28,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨29,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨30,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨31,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨32,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨33,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨34,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨35,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨36,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨37,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨38,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨39,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨40,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨41,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨42,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨43,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨44,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨45,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨46,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨47,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨48,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨49,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨50,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨51,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12746) (by norm_num)
        (q := 1 - (cell12746 ⟨52,by decide⟩).lower)
        (by norm_num [cell12746]) (by norm_num [cell12746])
      exact ⟨E.1,E.2.trans (by norm_num [cell12746])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12746

/-! Source-cell containment and simple scalar guards at 12746. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12746)
open BstLean.Part268 (cell12746)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12746 ⟨10,by decide⟩).lower ∧ (cell12746 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12746 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12746 ⟨11,by decide⟩).lower ∧ (cell12746 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12746 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12746 ⟨12,by decide⟩).lower ∧ (cell12746 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12746 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12746 ⟨13,by decide⟩).lower ∧ (cell12746 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12746 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12746 ⟨14,by decide⟩).lower ∧ (cell12746 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12746 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12746 ⟨15,by decide⟩).lower ∧ (cell12746 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12746 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12746 ⟨16,by decide⟩).lower ∧ (cell12746 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12746 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12746 ⟨17,by decide⟩).lower ∧ (cell12746 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12746 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12746 ⟨18,by decide⟩).lower ∧ (cell12746 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12746 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12746 ⟨19,by decide⟩).lower ∧ (cell12746 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12746 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12746 ⟨20,by decide⟩).lower ∧ (cell12746 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12746 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12746 ⟨21,by decide⟩).lower ∧ (cell12746 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12746 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12746 ⟨22,by decide⟩).lower ∧ (cell12746 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12746 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12746 ⟨23,by decide⟩).lower ∧ (cell12746 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12746 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12746 ⟨24,by decide⟩).lower ∧ (cell12746 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12746 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12746 ⟨25,by decide⟩).lower ∧ (cell12746 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12746 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12746 ⟨26,by decide⟩).lower ∧ (cell12746 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12746 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12746 ⟨27,by decide⟩).lower ∧ (cell12746 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12746 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12746 ⟨28,by decide⟩).lower ∧ (cell12746 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12746 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12746 ⟨29,by decide⟩).lower ∧ (cell12746 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12746 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12746 ⟨30,by decide⟩).lower ∧ (cell12746 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12746 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12746 ⟨31,by decide⟩).lower ∧ (cell12746 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12746 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12746 ⟨32,by decide⟩).lower ∧ (cell12746 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12746 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12746 ⟨33,by decide⟩).lower ∧ (cell12746 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12746 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12746 ⟨34,by decide⟩).lower ∧ (cell12746 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12746 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12746 ⟨35,by decide⟩).lower ∧ (cell12746 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12746 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12746 ⟨36,by decide⟩).lower ∧ (cell12746 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12746 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12746 ⟨37,by decide⟩).lower ∧ (cell12746 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12746 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12746 ⟨38,by decide⟩).lower ∧ (cell12746 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12746 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12746 ⟨39,by decide⟩).lower ∧ (cell12746 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12746 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12746 ⟨40,by decide⟩).lower ∧ (cell12746 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12746 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12746 ⟨41,by decide⟩).lower ∧ (cell12746 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12746 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12746 ⟨42,by decide⟩).lower ∧ (cell12746 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12746 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12746 ⟨43,by decide⟩).lower ∧ (cell12746 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12746 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12746 ⟨44,by decide⟩).lower ∧ (cell12746 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12746 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12746 ⟨45,by decide⟩).lower ∧ (cell12746 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12746 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12746 ⟨46,by decide⟩).lower ∧ (cell12746 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12746 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12746 ⟨47,by decide⟩).lower ∧ (cell12746 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12746 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12746 ⟨48,by decide⟩).lower ∧ (cell12746 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12746 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12746 ⟨49,by decide⟩).lower ∧ (cell12746 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12746 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12746 ⟨50,by decide⟩).lower ∧ (cell12746 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12746 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12746 ⟨51,by decide⟩).lower ∧ (cell12746 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12746 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12746 ⟨52,by decide⟩).lower ∧ (cell12746 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12746 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12746 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12746 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12746,cell12746,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12746 i).lower ∧
    (cell12746 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12746 i).upper ≤ (0.532 : ℝ) ∧
    (cell12746 i).centre ≤ (0.1 : ℝ) ∧ (cell12746 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12746 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12746 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12746

/-! The local source numeric instances at 12746 have no network premises. -/
namespace BstLean.Part269.N12746
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12746)
open BstLean.Part268 (cell12746)

noncomputable def sourceNumerics12746 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12746 (cell12746 i)
      scalarRow12746.M scalarRow12746.H scalarRow12746.xi := by
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
    energy_allowance := scalarRow12746.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12746]
    centre_nonneg := (scalarRow12746.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12746])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12746
/-! Actual 12747 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12747 ≤ (1.035742563082 : ℝ) := by
  have hr : (112.902612901562 : ℝ) ≤ √(12747 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.902612901562 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12747 12747 (11 / 1000) ≤
    (0.008466473813 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12747) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.902612901562 : ℝ) ≤ √(12747 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12747)
  have hdiv : K / √(12747 : ℝ) ≤ K / 112.902612901562 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.902612901562 ≤ (0.008466473813 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12747.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12747 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12747 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12747 := gPlus_lower 12747
end BstLean.Part269.N12747

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12747
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035742563081 : ℝ) ≤ wn 12747 := by
  have hn : √(12747 : ℝ) ≤ 112.902612901563 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12747 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.902612901563 ≤ 2 / √(12747 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250935999 : ℝ) ≤ rhoBar 12747 BstLean.Part154.csC ∧
    rhoBar 12747 BstLean.Part154.csC ≤ 0.000250936387 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035742563081 : ℝ) / (1.295212 * 12747) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035742563082 : ℝ) / (1.29521 * 12747) := by gcongr
      _ ≤ (0.000250936387 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12747 BstLean.Part154.csC) ≤ 0.001003808518 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12747 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) ≤ 0.000191666872 ∧
    cc1 (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) ≤ 0.000121958910 ∧
    cc2 (rhoBar 12747 BstLean.Part154.csC) ≤ 0.000070798090 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12747 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12747 BstLean.Part154.csC * nuR (rhoBar 12747 BstLean.Part154.csC)) ≤ 0.000501888517 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250936387 : ℝ) * 0.001003808518 := by gcongr
      _ ≤ (0.000501888517 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12747 BstLean.Part154.csC) * nuR (rhoBar 12747 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003808518 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12747 BstLean.Part154.csC) * rhoBar 12747 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250936387 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250936387 / 2 + 0.399 * 0.001003808518 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191666872 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501888517 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121958910 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250936387 / 1.414213562 := by gcongr
      _ ≤ (0.000070798090 : ℝ) := by norm_num

end BstLean.Part269.N12747

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12747
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) ≤ 1.58646E-7 := by
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12747 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12747 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191666872 : ℝ) ^ 2 + 0.000121958910 ^ 2 + 3 * 0.000070798090 ^ 2 +
        2 * 0.797885 * 0.000191666872 * 0.000121958910 + 2 * 0.000191666872 * 0.000070798090 +
        4 * 0.797885 * 0.000121958910 * 0.000070798090 := by gcongr
    _ ≤ (1.58646E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12747 BstLean.Part154.csC Θ ≤ 0.002619256151 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12747 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12747 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035742563082 * 1.58646E-7 / (0.000250935999 : ℝ) := by gcongr
    _ ≤ 0.002619256151 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12747 BstLean.Part154.csC Θ ≤ 0.002906019571 + 0.000661844051 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12747 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035742563082 : ℝ) * ((2 * Θ * 0.000250936387 +
        (6863 / 10000) * 0.000250936387 * 12747 * 0.001003808518) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002906019571 + 0.000661844051 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12747 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12747 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12747 0.011 Θ ∧ gammaRatio 12747 0.011 Θ ≤ 0.000086265441 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12747 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035742563082 : ℝ) * 0.525 / ((1 - 0.011) * 12747) := by gcongr
      _ ≤ (0.000086265441 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12747 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12747 0.011 Θ) :=
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
    badAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12747 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12747 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12747 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12747 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12747 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12747 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12747 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12747 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12747 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12747 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035742563082 : ℝ) * 12747 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465103802 + 0.003281100202 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12747

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12747
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12747 BstLean.Part154.csC) (piBar (rhoBar 12747 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12747 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12747 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12747 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12747 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12747 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12747 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12747 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12747 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12747 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052386416655 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12747) ≤ 0.010577590283 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12747 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035742563082)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010577590283 + 2 * 0.737676 / 12747) := by gcongr
    _ ≤ (0.052386416655 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12747 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12747

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12747
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505685933 : ℝ) ≤ plow 12747 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12747) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694281409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375109480) : eMP 12747 0.011 xi bn ≤ 0.001183900993 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12747 : ℝ) * (1 - 0.011))) ≤ 0.000585384825 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375109480 / (12747 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585384825 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585384825 : ℝ) + 3.141593 * 0.052694281409 / (12747 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183900993 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694281409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375109480) : PiBarMP 12747 12 0.011 xi bn ≤ 0.160950338666 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12747 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037082468635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.279931421425 : ℝ) ≤ √((12747 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.902612901562 : ℝ) ≤ √(12747 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12747) ≤ 0.123402000226 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037082468635 + 0.052694281409 * 1.772454 / (2 * (112.279931421425 : ℝ))) * (1 + 0.001183900993) +
        8 / (12747 * 112.902612901562) + 0.123402000226 := by gcongr
    _ ≤ (0.160950338666 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694281409)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375109480) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281938766696) :
    parallelOracle 12747 0.011 xi bn cd ≤ 0.161936926560 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12747 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12747 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505685933 : ℝ) ≤ plow 12747 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.902612901562 : ℝ) ≤ √(12747 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281938766696 : ℝ) / (2 * 0.560505685933 * 112.902612901562)) * 0.160950338666 +
        0.281938766696 ^ 2 / (2 * 0.560505685933 * 112.902612901562) := by gcongr
    _ ≤ (0.161936926560 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694281409) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375109480)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281938766696) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12747 12747 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505685933 : ℝ) ≤ plow 12747 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.902612901562 : ℝ) ≤ √(12747 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12747 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12747 Θ 1.22 ≤ 0.011745525334 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.902612901562 := by gcongr <;> linarith
      _ ≤ (0.011745525334 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12747 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12747 12747 0.011 ≤ 0.008466473813 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12747 12747 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12747 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12747 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12747 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12747 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161936926560 + 0.011745525334 + (0.008466473813 : ℝ) *
        (1 + 2 * (0.281938766696 + 0.011745525334) / (0.560505685933 * 112.902612901562))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12747]

end BstLean.Part269.N12747

/-! The original eight local profiles supply actual 12747 moment certificates. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12747 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052694281409 ∧
    0 ≤ bN 12747 BstLean.Part154.csC (groupTheta g) ∧ bN 12747 BstLean.Part154.csC (groupTheta g) ≤ 0.001375109480 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12747 12747 0.011
      (momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12747 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12747 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12747 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229552350041 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12747 0.011
      (momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12747 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12747
/-! The actual computed-centre upper energy formula at 12747. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12747

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12747)
open BstLean.Part268 (cell12747)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085354368868
  | 2 => 0.086294648096
  | 3 => 0.087232710913
  | 4 => 0.088169893059
  | 5 => 0.089107812849
  | 6 => 0.090048413494
  | 7 => 0.090994009457
  | 8 => 0.091947336915
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12747 12747 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12747 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12747

/-! Actual upper energy certificates on all 43 source endpoints at 12747. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12747)
open BstLean.Part268 (cell12747)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12747 (gMinus 12747) (1 - (cell12747 i).lower) ≤ 1 ∧
    energyUpper 12747 (gMinus 12747) (BstLean.Part211.gPlus 12747)
      (finiteEnergy 12747 12747 0.011) (1 - (cell12747 i).lower) ≤
      (cell12747 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨10,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨11,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨12,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨13,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨14,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨15,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨16,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨17,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨18,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨19,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨20,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨21,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨22,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨23,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨24,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨25,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨26,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨27,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨28,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨29,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨30,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨31,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨32,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨33,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨34,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨35,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨36,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨37,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨38,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨39,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨40,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨41,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨42,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨43,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨44,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨45,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨46,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨47,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨48,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨49,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨50,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨51,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12747) (by norm_num)
        (q := 1 - (cell12747 ⟨52,by decide⟩).lower)
        (by norm_num [cell12747]) (by norm_num [cell12747])
      exact ⟨E.1,E.2.trans (by norm_num [cell12747])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12747

/-! Source-cell containment and simple scalar guards at 12747. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12747)
open BstLean.Part268 (cell12747)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12747 ⟨10,by decide⟩).lower ∧ (cell12747 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12747 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12747 ⟨11,by decide⟩).lower ∧ (cell12747 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12747 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12747 ⟨12,by decide⟩).lower ∧ (cell12747 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12747 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12747 ⟨13,by decide⟩).lower ∧ (cell12747 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12747 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12747 ⟨14,by decide⟩).lower ∧ (cell12747 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12747 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12747 ⟨15,by decide⟩).lower ∧ (cell12747 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12747 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12747 ⟨16,by decide⟩).lower ∧ (cell12747 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12747 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12747 ⟨17,by decide⟩).lower ∧ (cell12747 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12747 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12747 ⟨18,by decide⟩).lower ∧ (cell12747 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12747 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12747 ⟨19,by decide⟩).lower ∧ (cell12747 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12747 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12747 ⟨20,by decide⟩).lower ∧ (cell12747 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12747 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12747 ⟨21,by decide⟩).lower ∧ (cell12747 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12747 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12747 ⟨22,by decide⟩).lower ∧ (cell12747 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12747 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12747 ⟨23,by decide⟩).lower ∧ (cell12747 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12747 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12747 ⟨24,by decide⟩).lower ∧ (cell12747 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12747 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12747 ⟨25,by decide⟩).lower ∧ (cell12747 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12747 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12747 ⟨26,by decide⟩).lower ∧ (cell12747 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12747 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12747 ⟨27,by decide⟩).lower ∧ (cell12747 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12747 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12747 ⟨28,by decide⟩).lower ∧ (cell12747 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12747 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12747 ⟨29,by decide⟩).lower ∧ (cell12747 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12747 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12747 ⟨30,by decide⟩).lower ∧ (cell12747 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12747 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12747 ⟨31,by decide⟩).lower ∧ (cell12747 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12747 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12747 ⟨32,by decide⟩).lower ∧ (cell12747 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12747 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12747 ⟨33,by decide⟩).lower ∧ (cell12747 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12747 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12747 ⟨34,by decide⟩).lower ∧ (cell12747 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12747 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12747 ⟨35,by decide⟩).lower ∧ (cell12747 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12747 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12747 ⟨36,by decide⟩).lower ∧ (cell12747 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12747 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12747 ⟨37,by decide⟩).lower ∧ (cell12747 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12747 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12747 ⟨38,by decide⟩).lower ∧ (cell12747 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12747 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12747 ⟨39,by decide⟩).lower ∧ (cell12747 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12747 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12747 ⟨40,by decide⟩).lower ∧ (cell12747 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12747 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12747 ⟨41,by decide⟩).lower ∧ (cell12747 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12747 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12747 ⟨42,by decide⟩).lower ∧ (cell12747 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12747 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12747 ⟨43,by decide⟩).lower ∧ (cell12747 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12747 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12747 ⟨44,by decide⟩).lower ∧ (cell12747 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12747 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12747 ⟨45,by decide⟩).lower ∧ (cell12747 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12747 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12747 ⟨46,by decide⟩).lower ∧ (cell12747 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12747 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12747 ⟨47,by decide⟩).lower ∧ (cell12747 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12747 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12747 ⟨48,by decide⟩).lower ∧ (cell12747 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12747 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12747 ⟨49,by decide⟩).lower ∧ (cell12747 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12747 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12747 ⟨50,by decide⟩).lower ∧ (cell12747 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12747 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12747 ⟨51,by decide⟩).lower ∧ (cell12747 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12747 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12747 ⟨52,by decide⟩).lower ∧ (cell12747 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12747 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12747 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12747 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12747,cell12747,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12747 i).lower ∧
    (cell12747 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12747 i).upper ≤ (0.532 : ℝ) ∧
    (cell12747 i).centre ≤ (0.1 : ℝ) ∧ (cell12747 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12747 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12747 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12747

/-! The local source numeric instances at 12747 have no network premises. -/
namespace BstLean.Part269.N12747
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12747)
open BstLean.Part268 (cell12747)

noncomputable def sourceNumerics12747 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12747 (cell12747 i)
      scalarRow12747.M scalarRow12747.H scalarRow12747.xi := by
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
    energy_allowance := scalarRow12747.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12747]
    centre_nonneg := (scalarRow12747.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12747])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12747
/-! Actual 12748 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12748 ≤ (1.035741148858 : ℝ) := by
  have hr : (112.907041410179 : ℝ) ≤ √(12748 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.907041410179 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12748 12748 (11 / 1000) ≤
    (0.008466141733 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12748) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.907041410179 : ℝ) ≤ √(12748 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12748)
  have hdiv : K / √(12748 : ℝ) ≤ K / 112.907041410179 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.907041410179 ≤ (0.008466141733 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12748.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12748 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12748 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12748 := gPlus_lower 12748
end BstLean.Part269.N12748

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12748
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035741148857 : ℝ) ≤ wn 12748 := by
  have hn : √(12748 : ℝ) ≤ 112.907041410180 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12748 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.907041410180 ≤ 2 / √(12748 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250915972 : ℝ) ≤ rhoBar 12748 BstLean.Part154.csC ∧
    rhoBar 12748 BstLean.Part154.csC ≤ 0.000250916360 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035741148857 : ℝ) / (1.295212 * 12748) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035741148858 : ℝ) / (1.29521 * 12748) := by gcongr
      _ ≤ (0.000250916360 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12748 BstLean.Part154.csC) ≤ 0.001003728400 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12748 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) ≤ 0.000191651574 ∧
    cc1 (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) ≤ 0.000121949176 ∧
    cc2 (rhoBar 12748 BstLean.Part154.csC) ≤ 0.000070792440 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12748 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12748 BstLean.Part154.csC * nuR (rhoBar 12748 BstLean.Part154.csC)) ≤ 0.000501848460 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250916360 : ℝ) * 0.001003728400 := by gcongr
      _ ≤ (0.000501848460 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12748 BstLean.Part154.csC) * nuR (rhoBar 12748 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003728400 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12748 BstLean.Part154.csC) * rhoBar 12748 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250916360 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250916360 / 2 + 0.399 * 0.001003728400 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191651574 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501848460 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121949176 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250916360 / 1.414213562 := by gcongr
      _ ≤ (0.000070792440 : ℝ) := by norm_num

end BstLean.Part269.N12748

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12748
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) ≤ 1.58621E-7 := by
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12748 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12748 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191651574 : ℝ) ^ 2 + 0.000121949176 ^ 2 + 3 * 0.000070792440 ^ 2 +
        2 * 0.797885 * 0.000191651574 * 0.000121949176 + 2 * 0.000191651574 * 0.000070792440 +
        4 * 0.797885 * 0.000121949176 * 0.000070792440 := by gcongr
    _ ≤ (1.58621E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12748 BstLean.Part154.csC Θ ≤ 0.002619048847 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12748 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12748 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035741148858 * 1.58621E-7 / (0.000250915972 : ℝ) := by gcongr
    _ ≤ 0.002619048847 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12748 BstLean.Part154.csC Θ ≤ 0.002905779694 + 0.000661790326 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12748 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035741148858 : ℝ) * ((2 * Θ * 0.000250916360 +
        (6863 / 10000) * 0.000250916360 * 12748 * 0.001003728400) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002905779694 + 0.000661790326 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12748 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12748 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12748 0.011 Θ ∧ gammaRatio 12748 0.011 Θ ≤ 0.000086258556 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12748 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035741148858 : ℝ) * 0.525 / ((1 - 0.011) * 12748) := by gcongr
      _ ≤ (0.000086258556 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12748 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12748 0.011 Θ) :=
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
    badAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12748 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12748 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12748 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12748 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12748 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12748 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12748 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12748 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12748 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12748 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035741148858 : ℝ) * 12748 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464863925 + 0.003280839173 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12748

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12748
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12748 BstLean.Part154.csC) (piBar (rhoBar 12748 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12748 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12748 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12748 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12748 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12748 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12748 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12748 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12748 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12748 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052384339683 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12748) ≤ 0.010577175402 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12748 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035741148858)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010577175402 + 2 * 0.737676 / 12748) := by gcongr
    _ ≤ (0.052384339683 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12748 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12748

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12748
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505730820 : ℝ) ≤ plow 12748 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12748) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693904491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375000645) : eMP 12748 0.011 xi bn ≤ 0.001183807619 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12748 : ℝ) * (1 - 0.011))) ≤ 0.000585338700 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001375000645 / (12748 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585338700 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585338700 : ℝ) + 3.141593 * 0.052693904491 / (12748 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183807619 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693904491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375000645) : PiBarMP 12748 12 0.011 xi bn ≤ 0.160944005812 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12748 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037081001133 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.284335505893 : ℝ) ≤ √((12748 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.907041410179 : ℝ) ≤ √(12748 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12748) ≤ 0.123397160078 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037081001133 + 0.052693904491 * 1.772454 / (2 * (112.284335505893 : ℝ))) * (1 + 0.001183807619) +
        8 / (12748 * 112.907041410179) + 0.123397160078 := by gcongr
    _ ≤ (0.160944005812 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693904491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375000645) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281935868737) :
    parallelOracle 12748 0.011 xi bn cd ≤ 0.161930524228 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12748 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12748 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505730820 : ℝ) ≤ plow 12748 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.907041410179 : ℝ) ≤ √(12748 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281935868737 : ℝ) / (2 * 0.560505730820 * 112.907041410179)) * 0.160944005812 +
        0.281935868737 ^ 2 / (2 * 0.560505730820 * 112.907041410179) := by gcongr
    _ ≤ (0.161930524228 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693904491) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001375000645)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281935868737) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12748 12748 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505730820 : ℝ) ≤ plow 12748 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.907041410179 : ℝ) ≤ √(12748 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12748 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12748 Θ 1.22 ≤ 0.011745064643 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.907041410179 := by gcongr <;> linarith
      _ ≤ (0.011745064643 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12748 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12748 12748 0.011 ≤ 0.008466141733 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12748 12748 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12748 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12748 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12748 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12748 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161930524228 + 0.011745064643 + (0.008466141733 : ℝ) *
        (1 + 2 * (0.281935868737 + 0.011745064643) / (0.560505730820 * 112.907041410179))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12748]

end BstLean.Part269.N12748

/-! The original eight local profiles supply actual 12748 moment certificates. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12748 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052693904491 ∧
    0 ≤ bN 12748 BstLean.Part154.csC (groupTheta g) ∧ bN 12748 BstLean.Part154.csC (groupTheta g) ≤ 0.001375000645 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12748 12748 0.011
      (momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12748 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12748 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12748 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229551529054 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12748 0.011
      (momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12748 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12748
/-! The actual computed-centre upper energy formula at 12748. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12748

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12748)
open BstLean.Part268 (cell12748)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085351502847
  | 2 => 0.086291730546
  | 3 => 0.087229734500
  | 4 => 0.088166848745
  | 5 => 0.089104689594
  | 6 => 0.090045197910
  | 7 => 0.090990685430
  | 8 => 0.091943885180
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12748 12748 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12748 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12748

/-! Actual upper energy certificates on all 43 source endpoints at 12748. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12748)
open BstLean.Part268 (cell12748)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12748 (gMinus 12748) (1 - (cell12748 i).lower) ≤ 1 ∧
    energyUpper 12748 (gMinus 12748) (BstLean.Part211.gPlus 12748)
      (finiteEnergy 12748 12748 0.011) (1 - (cell12748 i).lower) ≤
      (cell12748 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨10,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨11,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨12,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨13,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨14,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨15,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨16,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨17,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨18,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨19,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨20,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨21,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨22,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨23,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨24,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨25,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨26,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨27,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨28,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨29,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨30,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨31,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨32,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨33,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨34,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨35,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨36,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨37,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨38,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨39,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨40,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨41,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨42,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨43,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨44,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨45,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨46,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨47,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨48,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨49,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨50,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨51,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12748) (by norm_num)
        (q := 1 - (cell12748 ⟨52,by decide⟩).lower)
        (by norm_num [cell12748]) (by norm_num [cell12748])
      exact ⟨E.1,E.2.trans (by norm_num [cell12748])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12748

/-! Source-cell containment and simple scalar guards at 12748. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12748)
open BstLean.Part268 (cell12748)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12748 ⟨10,by decide⟩).lower ∧ (cell12748 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12748 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12748 ⟨11,by decide⟩).lower ∧ (cell12748 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12748 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12748 ⟨12,by decide⟩).lower ∧ (cell12748 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12748 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12748 ⟨13,by decide⟩).lower ∧ (cell12748 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12748 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12748 ⟨14,by decide⟩).lower ∧ (cell12748 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12748 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12748 ⟨15,by decide⟩).lower ∧ (cell12748 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12748 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12748 ⟨16,by decide⟩).lower ∧ (cell12748 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12748 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12748 ⟨17,by decide⟩).lower ∧ (cell12748 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12748 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12748 ⟨18,by decide⟩).lower ∧ (cell12748 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12748 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12748 ⟨19,by decide⟩).lower ∧ (cell12748 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12748 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12748 ⟨20,by decide⟩).lower ∧ (cell12748 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12748 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12748 ⟨21,by decide⟩).lower ∧ (cell12748 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12748 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12748 ⟨22,by decide⟩).lower ∧ (cell12748 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12748 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12748 ⟨23,by decide⟩).lower ∧ (cell12748 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12748 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12748 ⟨24,by decide⟩).lower ∧ (cell12748 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12748 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12748 ⟨25,by decide⟩).lower ∧ (cell12748 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12748 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12748 ⟨26,by decide⟩).lower ∧ (cell12748 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12748 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12748 ⟨27,by decide⟩).lower ∧ (cell12748 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12748 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12748 ⟨28,by decide⟩).lower ∧ (cell12748 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12748 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12748 ⟨29,by decide⟩).lower ∧ (cell12748 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12748 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12748 ⟨30,by decide⟩).lower ∧ (cell12748 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12748 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12748 ⟨31,by decide⟩).lower ∧ (cell12748 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12748 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12748 ⟨32,by decide⟩).lower ∧ (cell12748 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12748 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12748 ⟨33,by decide⟩).lower ∧ (cell12748 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12748 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12748 ⟨34,by decide⟩).lower ∧ (cell12748 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12748 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12748 ⟨35,by decide⟩).lower ∧ (cell12748 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12748 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12748 ⟨36,by decide⟩).lower ∧ (cell12748 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12748 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12748 ⟨37,by decide⟩).lower ∧ (cell12748 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12748 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12748 ⟨38,by decide⟩).lower ∧ (cell12748 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12748 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12748 ⟨39,by decide⟩).lower ∧ (cell12748 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12748 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12748 ⟨40,by decide⟩).lower ∧ (cell12748 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12748 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12748 ⟨41,by decide⟩).lower ∧ (cell12748 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12748 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12748 ⟨42,by decide⟩).lower ∧ (cell12748 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12748 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12748 ⟨43,by decide⟩).lower ∧ (cell12748 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12748 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12748 ⟨44,by decide⟩).lower ∧ (cell12748 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12748 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12748 ⟨45,by decide⟩).lower ∧ (cell12748 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12748 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12748 ⟨46,by decide⟩).lower ∧ (cell12748 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12748 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12748 ⟨47,by decide⟩).lower ∧ (cell12748 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12748 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12748 ⟨48,by decide⟩).lower ∧ (cell12748 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12748 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12748 ⟨49,by decide⟩).lower ∧ (cell12748 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12748 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12748 ⟨50,by decide⟩).lower ∧ (cell12748 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12748 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12748 ⟨51,by decide⟩).lower ∧ (cell12748 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12748 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12748 ⟨52,by decide⟩).lower ∧ (cell12748 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12748 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12748 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12748 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12748,cell12748,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12748 i).lower ∧
    (cell12748 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12748 i).upper ≤ (0.532 : ℝ) ∧
    (cell12748 i).centre ≤ (0.1 : ℝ) ∧ (cell12748 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12748 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12748 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12748

/-! The local source numeric instances at 12748 have no network premises. -/
namespace BstLean.Part269.N12748
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12748)
open BstLean.Part268 (cell12748)

noncomputable def sourceNumerics12748 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12748 (cell12748 i)
      scalarRow12748.M scalarRow12748.H scalarRow12748.xi := by
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
    energy_allowance := scalarRow12748.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12748]
    centre_nonneg := (scalarRow12748.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12748])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12748
/-! Actual 12749 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12749 ≤ (1.035739734802 : ℝ) := by
  have hr : (112.911469745106 : ℝ) ≤ √(12749 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.911469745106 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12749 12749 (11 / 1000) ≤
    (0.008465809693 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12749) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.911469745106 : ℝ) ≤ √(12749 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12749)
  have hdiv : K / √(12749 : ℝ) ≤ K / 112.911469745106 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.911469745106 ≤ (0.008465809693 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12749.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12749 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12749 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12749 := gPlus_lower 12749
end BstLean.Part269.N12749

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12749
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035739734801 : ℝ) ≤ wn 12749 := by
  have hn : √(12749 : ℝ) ≤ 112.911469745107 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12749 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.911469745107 ≤ 2 / √(12749 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250895948 : ℝ) ≤ rhoBar 12749 BstLean.Part154.csC ∧
    rhoBar 12749 BstLean.Part154.csC ≤ 0.000250896336 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035739734801 : ℝ) / (1.295212 * 12749) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035739734802 : ℝ) / (1.29521 * 12749) := by gcongr
      _ ≤ (0.000250896336 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12749 BstLean.Part154.csC) ≤ 0.001003648293 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12749 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) ≤ 0.000191636279 ∧
    cc1 (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) ≤ 0.000121939444 ∧
    cc2 (rhoBar 12749 BstLean.Part154.csC) ≤ 0.000070786790 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12749 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12749 BstLean.Part154.csC * nuR (rhoBar 12749 BstLean.Part154.csC)) ≤ 0.000501808410 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250896336 : ℝ) * 0.001003648293 := by gcongr
      _ ≤ (0.000501808410 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12749 BstLean.Part154.csC) * nuR (rhoBar 12749 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003648293 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12749 BstLean.Part154.csC) * rhoBar 12749 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250896336 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250896336 / 2 + 0.399 * 0.001003648293 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191636279 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501808410 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121939444 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250896336 / 1.414213562 := by gcongr
      _ ≤ (0.000070786790 : ℝ) := by norm_num

end BstLean.Part269.N12749

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12749
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) ≤ 1.58596E-7 := by
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12749 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12749 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191636279 : ℝ) ^ 2 + 0.000121939444 ^ 2 + 3 * 0.000070786790 ^ 2 +
        2 * 0.797885 * 0.000191636279 * 0.000121939444 + 2 * 0.000191636279 * 0.000070786790 +
        4 * 0.797885 * 0.000121939444 * 0.000070786790 := by gcongr
    _ ≤ (1.58596E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12749 BstLean.Part154.csC Θ ≤ 0.002618841481 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12749 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12749 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035739734802 * 1.58596E-7 / (0.000250895948 : ℝ) := by gcongr
    _ ≤ 0.002618841481 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12749 BstLean.Part154.csC Θ ≤ 0.002905539849 + 0.000661736609 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12749 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035739734802 : ℝ) * ((2 * Θ * 0.000250896336 +
        (6863 / 10000) * 0.000250896336 * 12749 * 0.001003648293) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002905539849 + 0.000661736609 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12749 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12749 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12749 0.011 Θ ∧ gammaRatio 12749 0.011 Θ ≤ 0.000086251673 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12749 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035739734802 : ℝ) * 0.525 / ((1 - 0.011) * 12749) := by gcongr
      _ ≤ (0.000086251673 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12749 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12749 0.011 Θ) :=
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
    badAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000559084231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12749 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12749 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12749 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12749 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12749 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12749 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12749 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12749 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12749 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12749 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035739734802 : ℝ) * 12749 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000559084231 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464624080 + 0.003280578090 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12749

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12749
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12749 BstLean.Part154.csC) (piBar (rhoBar 12749 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12749 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12749 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12749 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12749 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12749 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12749 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12749 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12749 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12749 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052382262958 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12749) ≤ 0.010576760570 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12749 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035739734802)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010576760570 + 2 * 0.737676 / 12749) := by gcongr
    _ ≤ (0.052382262958 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12749 12 ≤ 0.0015 := by
  exact BstLean.Part269.S15.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12749

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12749
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505775700 : ℝ) ≤ plow 12749 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12749) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693527578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374891778) : eMP 12749 0.011 xi bn ≤ 0.001183714237 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12749 : ℝ) * (1 - 0.011))) ≤ 0.000585292571 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374891778 / (12749 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585292571 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585292571 : ℝ) + 3.141593 * 0.052693527578 / (12749 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183714237 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693527578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374891778) : PiBarMP 12749 12 0.011 xi bn ≤ 0.160937673040 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12749 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037079533142 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.288739417628 : ℝ) ≤ √((12749 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.911469745106 : ℝ) ≤ √(12749 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12749) ≤ 0.123392320499 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037079533142 + 0.052693527578 * 1.772454 / (2 * (112.288739417628 : ℝ))) * (1 + 0.001183714237) +
        8 / (12749 * 112.911469745106) + 0.123392320499 := by gcongr
    _ ≤ (0.160937673040 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693527578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374891778) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281932971034) :
    parallelOracle 12749 0.011 xi bn cd ≤ 0.161924121987 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12749 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12749 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505775700 : ℝ) ≤ plow 12749 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.911469745106 : ℝ) ≤ √(12749 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281932971034 : ℝ) / (2 * 0.560505775700 * 112.911469745106)) * 0.160937673040 +
        0.281932971034 ^ 2 / (2 * 0.560505775700 * 112.911469745106) := by gcongr
    _ ≤ (0.161924121987 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693527578) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374891778)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281932971034) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12749 12749 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505775700 : ℝ) ≤ plow 12749 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.911469745106 : ℝ) ≤ √(12749 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12749 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12749 Θ 1.22 ≤ 0.011744604007 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.911469745106 := by gcongr <;> linarith
      _ ≤ (0.011744604007 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12749 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12749 12749 0.011 ≤ 0.008465809693 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12749 12749 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12749 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12749 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12749 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12749 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161924121987 + 0.011744604007 + (0.008465809693 : ℝ) *
        (1 + 2 * (0.281932971034 + 0.011744604007) / (0.560505775700 * 112.911469745106))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12749]

end BstLean.Part269.N12749

/-! The original eight local profiles supply actual 12749 moment certificates. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12749 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052693527578 ∧
    0 ≤ bN 12749 BstLean.Part154.csC (groupTheta g) ∧ bN 12749 BstLean.Part154.csC (groupTheta g) ≤ 0.001374891778 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12749 12749 0.011
      (momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12749 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12749 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12749 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229550708076 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12749 0.011
      (momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12749 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12749
/-! The actual computed-centre upper energy formula at 12749. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12749

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12749)
open BstLean.Part268 (cell12749)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085348637859
  | 2 => 0.086288814071
  | 3 => 0.087226759213
  | 4 => 0.088163805622
  | 5 => 0.089101567606
  | 6 => 0.090041983687
  | 7 => 0.090987362879
  | 8 => 0.091940435058
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12749 12749 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12749 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003470390978 + 0.003286976976 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S15.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S15.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12749

/-! Actual upper energy certificates on all 43 source endpoints at 12749. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12749)
open BstLean.Part268 (cell12749)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12749 (gMinus 12749) (1 - (cell12749 i).lower) ≤ 1 ∧
    energyUpper 12749 (gMinus 12749) (BstLean.Part211.gPlus 12749)
      (finiteEnergy 12749 12749 0.011) (1 - (cell12749 i).lower) ≤
      (cell12749 i).energy := by
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
      have E := BstLean.Part269.S15.uniformEnergy10 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨10,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy11 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨11,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy12 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨12,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy13 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨13,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy14 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨14,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy15 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨15,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy16 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨16,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy17 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨17,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy18 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨18,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy19 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨19,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy20 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨20,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy21 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨21,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy22 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨22,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy23 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨23,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy24 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨24,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy25 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨25,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy26 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨26,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy27 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨27,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy28 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨28,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy29 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨29,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy30 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨30,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy31 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨31,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy32 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨32,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy33 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨33,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy34 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨34,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy35 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨35,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy36 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨36,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy37 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨37,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy38 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨38,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy39 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨39,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy40 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨40,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy41 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨41,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy42 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨42,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy43 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨43,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy44 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨44,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy45 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨45,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy46 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨46,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy47 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨47,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy48 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨48,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy49 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨49,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy50 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨50,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy51 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨51,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S15.uniformEnergy52 (n := 12749) (by norm_num)
        (q := 1 - (cell12749 ⟨52,by decide⟩).lower)
        (by norm_num [cell12749]) (by norm_num [cell12749])
      exact ⟨E.1,E.2.trans (by norm_num [cell12749])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12749

/-! Source-cell containment and simple scalar guards at 12749. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12749)
open BstLean.Part268 (cell12749)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12749 ⟨10,by decide⟩).lower ∧ (cell12749 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12749 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12749 ⟨11,by decide⟩).lower ∧ (cell12749 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12749 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12749 ⟨12,by decide⟩).lower ∧ (cell12749 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12749 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12749 ⟨13,by decide⟩).lower ∧ (cell12749 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12749 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12749 ⟨14,by decide⟩).lower ∧ (cell12749 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12749 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12749 ⟨15,by decide⟩).lower ∧ (cell12749 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12749 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12749 ⟨16,by decide⟩).lower ∧ (cell12749 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12749 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12749 ⟨17,by decide⟩).lower ∧ (cell12749 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12749 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12749 ⟨18,by decide⟩).lower ∧ (cell12749 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12749 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12749 ⟨19,by decide⟩).lower ∧ (cell12749 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12749 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12749 ⟨20,by decide⟩).lower ∧ (cell12749 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12749 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12749 ⟨21,by decide⟩).lower ∧ (cell12749 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12749 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12749 ⟨22,by decide⟩).lower ∧ (cell12749 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12749 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12749 ⟨23,by decide⟩).lower ∧ (cell12749 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12749 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12749 ⟨24,by decide⟩).lower ∧ (cell12749 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12749 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12749 ⟨25,by decide⟩).lower ∧ (cell12749 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12749 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12749 ⟨26,by decide⟩).lower ∧ (cell12749 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12749 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12749 ⟨27,by decide⟩).lower ∧ (cell12749 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12749 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12749 ⟨28,by decide⟩).lower ∧ (cell12749 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12749 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12749 ⟨29,by decide⟩).lower ∧ (cell12749 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12749 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12749 ⟨30,by decide⟩).lower ∧ (cell12749 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12749 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12749 ⟨31,by decide⟩).lower ∧ (cell12749 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12749 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12749 ⟨32,by decide⟩).lower ∧ (cell12749 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12749 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12749 ⟨33,by decide⟩).lower ∧ (cell12749 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12749 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12749 ⟨34,by decide⟩).lower ∧ (cell12749 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12749 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12749 ⟨35,by decide⟩).lower ∧ (cell12749 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12749 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12749 ⟨36,by decide⟩).lower ∧ (cell12749 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12749 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12749 ⟨37,by decide⟩).lower ∧ (cell12749 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12749 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12749 ⟨38,by decide⟩).lower ∧ (cell12749 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12749 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12749 ⟨39,by decide⟩).lower ∧ (cell12749 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12749 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12749 ⟨40,by decide⟩).lower ∧ (cell12749 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12749 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12749 ⟨41,by decide⟩).lower ∧ (cell12749 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12749 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12749 ⟨42,by decide⟩).lower ∧ (cell12749 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12749 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12749 ⟨43,by decide⟩).lower ∧ (cell12749 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12749 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12749 ⟨44,by decide⟩).lower ∧ (cell12749 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12749 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12749 ⟨45,by decide⟩).lower ∧ (cell12749 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12749 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12749 ⟨46,by decide⟩).lower ∧ (cell12749 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12749 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12749 ⟨47,by decide⟩).lower ∧ (cell12749 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12749 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12749 ⟨48,by decide⟩).lower ∧ (cell12749 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12749 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12749 ⟨49,by decide⟩).lower ∧ (cell12749 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12749 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12749 ⟨50,by decide⟩).lower ∧ (cell12749 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12749 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12749 ⟨51,by decide⟩).lower ∧ (cell12749 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12749 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12749 ⟨52,by decide⟩).lower ∧ (cell12749 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12749 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12749 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12749 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12749,cell12749,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12749 i).lower ∧
    (cell12749 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12749 i).upper ≤ (0.532 : ℝ) ∧
    (cell12749 i).centre ≤ (0.1 : ℝ) ∧ (cell12749 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12749 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12749 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12749

/-! The local source numeric instances at 12749 have no network premises. -/
namespace BstLean.Part269.N12749
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12749)
open BstLean.Part268 (cell12749)

noncomputable def sourceNumerics12749 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12749 (cell12749 i)
      scalarRow12749.M scalarRow12749.H scalarRow12749.xi := by
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
    energy_allowance := scalarRow12749.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12749]
    centre_nonneg := (scalarRow12749.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D15.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12749])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12749