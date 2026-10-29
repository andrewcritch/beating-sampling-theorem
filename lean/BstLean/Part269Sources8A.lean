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
/-! Actual 12550 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12550 ≤ (1.036024472514 : ℝ) := by
  have hr : (112.026782512040 : ℝ) ≤ √(12550 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.026782512040 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12550 12550 (11 / 1000) ≤
    (0.008532665597 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12550) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.026782512040 : ℝ) ≤ √(12550 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12550)
  have hdiv : K / √(12550 : ℝ) ≤ K / 112.026782512040 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.026782512040 ≤ (0.008532665597 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12550.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12550 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12550 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12550 := gPlus_lower 12550
end BstLean.Part269.N12550

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12550
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036024472513 : ℝ) ≤ wn 12550 := by
  have hn : √(12550 : ℝ) ≤ 112.026782512041 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12550 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.026782512041 ≤ 2 / √(12550 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254944366 : ℝ) ≤ rhoBar 12550 BstLean.Part154.csC ∧
    rhoBar 12550 BstLean.Part154.csC ≤ 0.000254944761 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036024472513 : ℝ) / (1.295212 * 12550) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036024472514 : ℝ) / (1.29521 * 12550) := by gcongr
      _ ≤ (0.000254944761 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12550 BstLean.Part154.csC) ≤ 0.001019844041 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12550 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) ≤ 0.000194728638 ∧
    cc1 (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) ≤ 0.000123907103 ∧
    cc2 (rhoBar 12550 BstLean.Part154.csC) ≤ 0.000071928995 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12550 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12550 BstLean.Part154.csC * nuR (rhoBar 12550 BstLean.Part154.csC)) ≤ 0.000509905771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254944761 : ℝ) * 0.001019844041 := by gcongr
      _ ≤ (0.000509905771 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12550 BstLean.Part154.csC) * nuR (rhoBar 12550 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019844041 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12550 BstLean.Part154.csC) * rhoBar 12550 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254944761 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254944761 / 2 + 0.399 * 0.001019844041 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194728638 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509905771 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123907103 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254944761 / 1.414213562 := by gcongr
      _ ≤ (0.000071928995 : ℝ) := by norm_num

end BstLean.Part269.N12550

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12550
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) ≤ 1.63755E-7 := by
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12550 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12550 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194728638 : ℝ) ^ 2 + 0.000123907103 ^ 2 + 3 * 0.000071928995 ^ 2 +
        2 * 0.797885 * 0.000194728638 * 0.000123907103 + 2 * 0.000194728638 * 0.000071928995 +
        4 * 0.797885 * 0.000123907103 * 0.000071928995 := by gcongr
    _ ≤ (1.63755E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12550 BstLean.Part154.csC Θ ≤ 0.002661822894 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12550 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12550 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036024472514 * 1.63755E-7 / (0.000254944366 : ℝ) := by gcongr
    _ ≤ 0.002661822894 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12550 BstLean.Part154.csC Θ ≤ 0.002954049732 + 0.000672599145 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12550 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036024472514 : ℝ) * ((2 * Θ * 0.000254944761 +
        (6863 / 10000) * 0.000254944761 * 12550 * 0.001019844041) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002954049732 + 0.000672599145 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12550 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12550 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12550 0.011 Θ ∧ gammaRatio 12550 0.011 Θ ≤ 0.000087643416 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12550 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036024472514 : ℝ) * 0.525 / ((1 - 0.011) * 12550) := by gcongr
      _ ≤ (0.000087643416 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12550 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12550 0.011 Θ) :=
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
    badAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12550 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12550 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12550 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12550 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12550 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12550 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12550 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12550 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12550 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12550 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036024472514 : ℝ) * 12550 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697790472 + 0.003334422039 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12550

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12550
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12550 BstLean.Part154.csC) (piBar (rhoBar 12550 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12550 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12550 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12550 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12550 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12550 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12550 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12550 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12550 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12550 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052800443592 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12550) ≤ 0.010660286356 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12550 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036024472514)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010660286356 + 2 * 0.737676 / 12550) := by gcongr
    _ ≤ (0.052800443592 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12550 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12550

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12550
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496703768 : ℝ) ≤ plow 12550 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12550) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954962043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397457020) : eMP 12550 0.011 xi bn ≤ 0.001202875323 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12550 : ℝ) * (1 - 0.011))) ≤ 0.000594735937 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397457020 / (12550 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594735937 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594735937 : ℝ) + 3.141593 * 0.052954962043 / (12550 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202875323 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954962043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397457020) : PiBarMP 12550 12 0.011 xi bn ≤ 0.162221744403 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12550 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037382576423 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.408931419343 : ℝ) ≤ √((12550 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.026782512040 : ℝ) ≤ √(12550 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12550) ≤ 0.124366762576 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037382576423 + 0.052954962043 * 1.772454 / (2 * (111.408931419343 : ℝ))) * (1 + 0.001202875323) +
        8 / (12550 * 112.026782512040) + 0.124366762576 := by gcongr
    _ ≤ (0.162221744403 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954962043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397457020) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282919895276) :
    parallelOracle 12550 0.011 xi bn cd ≤ 0.163224596273 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12550 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12550 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496703768 : ℝ) ≤ plow 12550 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.026782512040 : ℝ) ≤ √(12550 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282919895276 : ℝ) / (2 * 0.560496703768 * 112.026782512040)) * 0.162221744403 +
        0.282919895276 ^ 2 / (2 * 0.560496703768 * 112.026782512040) := by gcongr
    _ ≤ (0.163224596273 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954962043) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397457020)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282919895276) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12550 12550 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496703768 : ℝ) ≤ plow 12550 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.026782512040 : ℝ) ≤ √(12550 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12550 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12550 Θ 1.22 ≤ 0.011837352375 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.026782512040 := by gcongr <;> linarith
      _ ≤ (0.011837352375 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12550 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12550 12550 0.011 ≤ 0.008532665597 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12550 12550 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12550 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12550 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12550 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12550 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163224596273 + 0.011837352375 + (0.008532665597 : ℝ) *
        (1 + 2 * (0.282919895276 + 0.011837352375) / (0.560496703768 * 112.026782512040))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12550]

end BstLean.Part269.N12550

/-! The original eight local profiles supply actual 12550 moment certificates. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12550 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052954962043 ∧
    0 ≤ bN 12550 BstLean.Part154.csC (groupTheta g) ∧ bN 12550 BstLean.Part154.csC (groupTheta g) ≤ 0.001397457020 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12550 12550 0.011
      (momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12550 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12550 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12550 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230119451684 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12550 0.011
      (momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12550 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12550
/-! The actual computed-centre upper energy formula at 12550. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12550

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12550)
open BstLean.Part268 (cell12550)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085940543460
  | 2 => 0.086891864203
  | 3 => 0.087842622543
  | 4 => 0.088794531979
  | 5 => 0.089749654705
  | 6 => 0.090710452036
  | 7 => 0.091679839329
  | 8 => 0.092661245393
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12550 12550 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12550 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12550

/-! Actual upper energy certificates on all 43 source endpoints at 12550. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12550)
open BstLean.Part268 (cell12550)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12550 (gMinus 12550) (1 - (cell12550 i).lower) ≤ 1 ∧
    energyUpper 12550 (gMinus 12550) (BstLean.Part211.gPlus 12550)
      (finiteEnergy 12550 12550 0.011) (1 - (cell12550 i).lower) ≤
      (cell12550 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨10,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨11,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨12,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨13,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨14,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨15,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨16,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨17,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨18,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨19,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨20,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨21,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨22,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨23,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨24,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨25,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨26,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨27,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨28,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨29,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨30,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨31,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨32,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨33,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨34,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨35,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨36,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨37,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨38,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨39,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨40,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨41,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨42,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨43,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨44,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨45,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨46,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨47,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨48,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨49,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨50,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨51,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12550) (by norm_num)
        (q := 1 - (cell12550 ⟨52,by decide⟩).lower)
        (by norm_num [cell12550]) (by norm_num [cell12550])
      exact ⟨E.1,E.2.trans (by norm_num [cell12550])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12550

/-! Source-cell containment and simple scalar guards at 12550. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12550)
open BstLean.Part268 (cell12550)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12550 ⟨10,by decide⟩).lower ∧ (cell12550 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12550 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12550 ⟨11,by decide⟩).lower ∧ (cell12550 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12550 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12550 ⟨12,by decide⟩).lower ∧ (cell12550 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12550 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12550 ⟨13,by decide⟩).lower ∧ (cell12550 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12550 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12550 ⟨14,by decide⟩).lower ∧ (cell12550 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12550 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12550 ⟨15,by decide⟩).lower ∧ (cell12550 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12550 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12550 ⟨16,by decide⟩).lower ∧ (cell12550 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12550 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12550 ⟨17,by decide⟩).lower ∧ (cell12550 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12550 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12550 ⟨18,by decide⟩).lower ∧ (cell12550 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12550 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12550 ⟨19,by decide⟩).lower ∧ (cell12550 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12550 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12550 ⟨20,by decide⟩).lower ∧ (cell12550 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12550 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12550 ⟨21,by decide⟩).lower ∧ (cell12550 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12550 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12550 ⟨22,by decide⟩).lower ∧ (cell12550 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12550 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12550 ⟨23,by decide⟩).lower ∧ (cell12550 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12550 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12550 ⟨24,by decide⟩).lower ∧ (cell12550 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12550 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12550 ⟨25,by decide⟩).lower ∧ (cell12550 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12550 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12550 ⟨26,by decide⟩).lower ∧ (cell12550 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12550 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12550 ⟨27,by decide⟩).lower ∧ (cell12550 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12550 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12550 ⟨28,by decide⟩).lower ∧ (cell12550 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12550 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12550 ⟨29,by decide⟩).lower ∧ (cell12550 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12550 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12550 ⟨30,by decide⟩).lower ∧ (cell12550 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12550 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12550 ⟨31,by decide⟩).lower ∧ (cell12550 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12550 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12550 ⟨32,by decide⟩).lower ∧ (cell12550 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12550 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12550 ⟨33,by decide⟩).lower ∧ (cell12550 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12550 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12550 ⟨34,by decide⟩).lower ∧ (cell12550 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12550 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12550 ⟨35,by decide⟩).lower ∧ (cell12550 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12550 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12550 ⟨36,by decide⟩).lower ∧ (cell12550 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12550 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12550 ⟨37,by decide⟩).lower ∧ (cell12550 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12550 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12550 ⟨38,by decide⟩).lower ∧ (cell12550 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12550 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12550 ⟨39,by decide⟩).lower ∧ (cell12550 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12550 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12550 ⟨40,by decide⟩).lower ∧ (cell12550 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12550 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12550 ⟨41,by decide⟩).lower ∧ (cell12550 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12550 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12550 ⟨42,by decide⟩).lower ∧ (cell12550 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12550 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12550 ⟨43,by decide⟩).lower ∧ (cell12550 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12550 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12550 ⟨44,by decide⟩).lower ∧ (cell12550 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12550 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12550 ⟨45,by decide⟩).lower ∧ (cell12550 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12550 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12550 ⟨46,by decide⟩).lower ∧ (cell12550 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12550 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12550 ⟨47,by decide⟩).lower ∧ (cell12550 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12550 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12550 ⟨48,by decide⟩).lower ∧ (cell12550 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12550 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12550 ⟨49,by decide⟩).lower ∧ (cell12550 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12550 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12550 ⟨50,by decide⟩).lower ∧ (cell12550 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12550 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12550 ⟨51,by decide⟩).lower ∧ (cell12550 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12550 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12550 ⟨52,by decide⟩).lower ∧ (cell12550 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12550 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12550 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12550 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12550,cell12550,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12550 i).lower ∧
    (cell12550 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12550 i).upper ≤ (0.532 : ℝ) ∧
    (cell12550 i).centre ≤ (0.1 : ℝ) ∧ (cell12550 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12550 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12550 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12550

/-! The local source numeric instances at 12550 have no network premises. -/
namespace BstLean.Part269.N12550
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12550)
open BstLean.Part268 (cell12550)

noncomputable def sourceNumerics12550 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12550 (cell12550 i)
      scalarRow12550.M scalarRow12550.H scalarRow12550.xi := by
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
    energy_allowance := scalarRow12550.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12550]
    centre_nonneg := (scalarRow12550.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12550])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12550
/-! Actual 12551 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12551 ≤ (1.036023024665 : ℝ) := by
  have hr : (112.031245641561 : ℝ) ≤ √(12551 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.031245641561 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12551 12551 (11 / 1000) ≤
    (0.008532325667 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12551) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.031245641561 : ℝ) ≤ √(12551 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12551)
  have hdiv : K / √(12551 : ℝ) ≤ K / 112.031245641561 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.031245641561 ≤ (0.008532325667 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12551.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12551 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12551 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12551 := gPlus_lower 12551
end BstLean.Part269.N12551

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12551
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036023024664 : ℝ) ≤ wn 12551 := by
  have hn : √(12551 : ℝ) ≤ 112.031245641562 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12551 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.031245641562 ≤ 2 / √(12551 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254923697 : ℝ) ≤ rhoBar 12551 BstLean.Part154.csC ∧
    rhoBar 12551 BstLean.Part154.csC ≤ 0.000254924092 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036023024664 : ℝ) / (1.295212 * 12551) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036023024665 : ℝ) / (1.29521 * 12551) := by gcongr
      _ ≤ (0.000254924092 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12551 BstLean.Part154.csC) ≤ 0.001019761355 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12551 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) ≤ 0.000194712851 ∧
    cc1 (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) ≤ 0.000123897057 ∧
    cc2 (rhoBar 12551 BstLean.Part154.csC) ≤ 0.000071923164 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12551 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12551 BstLean.Part154.csC * nuR (rhoBar 12551 BstLean.Part154.csC)) ≤ 0.000509864431 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254924092 : ℝ) * 0.001019761355 := by gcongr
      _ ≤ (0.000509864431 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12551 BstLean.Part154.csC) * nuR (rhoBar 12551 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019761355 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12551 BstLean.Part154.csC) * rhoBar 12551 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254924092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254924092 / 2 + 0.399 * 0.001019761355 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194712851 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509864431 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123897057 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254924092 / 1.414213562 := by gcongr
      _ ≤ (0.000071923164 : ℝ) := by norm_num

end BstLean.Part269.N12551

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12551
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) ≤ 1.63729E-7 := by
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12551 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12551 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194712851 : ℝ) ^ 2 + 0.000123897057 ^ 2 + 3 * 0.000071923164 ^ 2 +
        2 * 0.797885 * 0.000194712851 * 0.000123897057 + 2 * 0.000194712851 * 0.000071923164 +
        4 * 0.797885 * 0.000123897057 * 0.000071923164 := by gcongr
    _ ≤ (1.63729E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12551 BstLean.Part154.csC Θ ≤ 0.002661612331 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12551 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12551 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036023024665 * 1.63729E-7 / (0.000254923697 : ℝ) := by gcongr
    _ ≤ 0.002661612331 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12551 BstLean.Part154.csC Θ ≤ 0.002953801970 + 0.000672543676 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12551 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036023024665 : ℝ) * ((2 * Θ * 0.000254924092 +
        (6863 / 10000) * 0.000254924092 * 12551 * 0.001019761355) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002953801970 + 0.000672543676 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12551 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12551 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12551 0.011 Θ ∧ gammaRatio 12551 0.011 Θ ≤ 0.000087636311 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12551 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036023024665 : ℝ) * 0.525 / ((1 - 0.011) * 12551) := by gcongr
      _ ≤ (0.000087636311 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12551 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12551 0.011 Θ) :=
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
    badAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12551 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12551 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12551 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12551 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12551 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12551 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12551 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12551 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12551 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12551 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036023024665 : ℝ) * 12551 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697542710 + 0.003334156007 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12551

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12551
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12551 BstLean.Part154.csC) (piBar (rhoBar 12551 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12551 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12551 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12551 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12551 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12551 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12551 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12551 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12551 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12551 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052798317173 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12551) ≤ 0.010659861669 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12551 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036023024665)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010659861669 + 2 * 0.737676 / 12551) := by gcongr
    _ ≤ (0.052798317173 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12551 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12551

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12551
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496750075 : ℝ) ≤ plow 12551 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12551) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954574614)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397346474) : eMP 12551 0.011 xi bn ≤ 0.001202779725 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12551 : ℝ) * (1 - 0.011))) ≤ 0.000594688721 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397346474 / (12551 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594688721 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594688721 : ℝ) + 3.141593 * 0.052954574614 / (12551 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202779725 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954574614)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397346474) : PiBarMP 12551 12 0.011 xi bn ≤ 0.162215285283 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12551 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037381097817 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.413369933774 : ℝ) ≤ √((12551 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.031245641561 : ℝ) ≤ √(12551 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12551) ≤ 0.124361808021 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037381097817 + 0.052954574614 * 1.772454 / (2 * (111.413369933774 : ℝ))) * (1 + 0.001202779725) +
        8 / (12551 * 112.031245641561) + 0.124361808021 := by gcongr
    _ ≤ (0.162215285283 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954574614)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397346474) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282916927055) :
    parallelOracle 12551 0.011 xi bn cd ≤ 0.163218065360 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12551 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12551 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496750075 : ℝ) ≤ plow 12551 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.031245641561 : ℝ) ≤ √(12551 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282916927055 : ℝ) / (2 * 0.560496750075 * 112.031245641561)) * 0.162215285283 +
        0.282916927055 ^ 2 / (2 * 0.560496750075 * 112.031245641561) := by gcongr
    _ ≤ (0.163218065360 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954574614) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397346474)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282916927055) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12551 12551 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496750075 : ℝ) ≤ plow 12551 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.031245641561 : ℝ) ≤ √(12551 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12551 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12551 Θ 1.22 ≤ 0.011836880796 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.031245641561 := by gcongr <;> linarith
      _ ≤ (0.011836880796 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12551 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12551 12551 0.011 ≤ 0.008532325667 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12551 12551 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12551 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12551 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12551 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12551 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163218065360 + 0.011836880796 + (0.008532325667 : ℝ) *
        (1 + 2 * (0.282916927055 + 0.011836880796) / (0.560496750075 * 112.031245641561))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12551]

end BstLean.Part269.N12551

/-! The original eight local profiles supply actual 12551 moment certificates. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12551 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052954574614 ∧
    0 ≤ bN 12551 BstLean.Part154.csC (groupTheta g) ∧ bN 12551 BstLean.Part154.csC (groupTheta g) ≤ 0.001397346474 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12551 12551 0.011
      (momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12551 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12551 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12551 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230118609882 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12551 0.011
      (momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12551 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12551
/-! The actual computed-centre upper energy formula at 12551. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12551

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12551)
open BstLean.Part268 (cell12551)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085937452016
  | 2 => 0.086888711839
  | 3 => 0.087839399719
  | 4 => 0.088791227009
  | 5 => 0.089746253385
  | 6 => 0.090706937231
  | 7 => 0.091676190509
  | 8 => 0.092657438125
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12551 12551 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12551 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12551

/-! Actual upper energy certificates on all 43 source endpoints at 12551. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12551)
open BstLean.Part268 (cell12551)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12551 (gMinus 12551) (1 - (cell12551 i).lower) ≤ 1 ∧
    energyUpper 12551 (gMinus 12551) (BstLean.Part211.gPlus 12551)
      (finiteEnergy 12551 12551 0.011) (1 - (cell12551 i).lower) ≤
      (cell12551 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨10,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨11,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨12,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨13,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨14,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨15,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨16,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨17,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨18,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨19,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨20,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨21,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨22,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨23,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨24,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨25,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨26,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨27,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨28,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨29,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨30,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨31,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨32,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨33,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨34,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨35,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨36,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨37,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨38,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨39,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨40,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨41,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨42,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨43,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨44,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨45,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨46,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨47,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨48,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨49,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨50,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨51,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12551) (by norm_num)
        (q := 1 - (cell12551 ⟨52,by decide⟩).lower)
        (by norm_num [cell12551]) (by norm_num [cell12551])
      exact ⟨E.1,E.2.trans (by norm_num [cell12551])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12551

/-! Source-cell containment and simple scalar guards at 12551. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12551)
open BstLean.Part268 (cell12551)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12551 ⟨10,by decide⟩).lower ∧ (cell12551 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12551 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12551 ⟨11,by decide⟩).lower ∧ (cell12551 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12551 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12551 ⟨12,by decide⟩).lower ∧ (cell12551 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12551 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12551 ⟨13,by decide⟩).lower ∧ (cell12551 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12551 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12551 ⟨14,by decide⟩).lower ∧ (cell12551 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12551 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12551 ⟨15,by decide⟩).lower ∧ (cell12551 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12551 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12551 ⟨16,by decide⟩).lower ∧ (cell12551 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12551 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12551 ⟨17,by decide⟩).lower ∧ (cell12551 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12551 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12551 ⟨18,by decide⟩).lower ∧ (cell12551 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12551 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12551 ⟨19,by decide⟩).lower ∧ (cell12551 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12551 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12551 ⟨20,by decide⟩).lower ∧ (cell12551 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12551 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12551 ⟨21,by decide⟩).lower ∧ (cell12551 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12551 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12551 ⟨22,by decide⟩).lower ∧ (cell12551 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12551 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12551 ⟨23,by decide⟩).lower ∧ (cell12551 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12551 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12551 ⟨24,by decide⟩).lower ∧ (cell12551 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12551 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12551 ⟨25,by decide⟩).lower ∧ (cell12551 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12551 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12551 ⟨26,by decide⟩).lower ∧ (cell12551 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12551 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12551 ⟨27,by decide⟩).lower ∧ (cell12551 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12551 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12551 ⟨28,by decide⟩).lower ∧ (cell12551 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12551 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12551 ⟨29,by decide⟩).lower ∧ (cell12551 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12551 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12551 ⟨30,by decide⟩).lower ∧ (cell12551 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12551 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12551 ⟨31,by decide⟩).lower ∧ (cell12551 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12551 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12551 ⟨32,by decide⟩).lower ∧ (cell12551 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12551 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12551 ⟨33,by decide⟩).lower ∧ (cell12551 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12551 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12551 ⟨34,by decide⟩).lower ∧ (cell12551 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12551 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12551 ⟨35,by decide⟩).lower ∧ (cell12551 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12551 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12551 ⟨36,by decide⟩).lower ∧ (cell12551 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12551 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12551 ⟨37,by decide⟩).lower ∧ (cell12551 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12551 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12551 ⟨38,by decide⟩).lower ∧ (cell12551 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12551 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12551 ⟨39,by decide⟩).lower ∧ (cell12551 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12551 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12551 ⟨40,by decide⟩).lower ∧ (cell12551 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12551 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12551 ⟨41,by decide⟩).lower ∧ (cell12551 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12551 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12551 ⟨42,by decide⟩).lower ∧ (cell12551 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12551 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12551 ⟨43,by decide⟩).lower ∧ (cell12551 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12551 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12551 ⟨44,by decide⟩).lower ∧ (cell12551 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12551 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12551 ⟨45,by decide⟩).lower ∧ (cell12551 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12551 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12551 ⟨46,by decide⟩).lower ∧ (cell12551 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12551 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12551 ⟨47,by decide⟩).lower ∧ (cell12551 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12551 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12551 ⟨48,by decide⟩).lower ∧ (cell12551 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12551 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12551 ⟨49,by decide⟩).lower ∧ (cell12551 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12551 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12551 ⟨50,by decide⟩).lower ∧ (cell12551 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12551 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12551 ⟨51,by decide⟩).lower ∧ (cell12551 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12551 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12551 ⟨52,by decide⟩).lower ∧ (cell12551 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12551 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12551 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12551 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12551,cell12551,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12551 i).lower ∧
    (cell12551 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12551 i).upper ≤ (0.532 : ℝ) ∧
    (cell12551 i).centre ≤ (0.1 : ℝ) ∧ (cell12551 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12551 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12551 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12551

/-! The local source numeric instances at 12551 have no network premises. -/
namespace BstLean.Part269.N12551
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12551)
open BstLean.Part268 (cell12551)

noncomputable def sourceNumerics12551 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12551 (cell12551 i)
      scalarRow12551.M scalarRow12551.H scalarRow12551.xi := by
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
    energy_allowance := scalarRow12551.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12551]
    centre_nonneg := (scalarRow12551.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12551])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12551
/-! Actual 12552 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12552 ≤ (1.036021576990 : ℝ) := by
  have hr : (112.035708593287 : ℝ) ≤ √(12552 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.035708593287 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12552 12552 (11 / 1000) ≤
    (0.008531985779 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12552) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.035708593287 : ℝ) ≤ √(12552 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12552)
  have hdiv : K / √(12552 : ℝ) ≤ K / 112.035708593287 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.035708593287 ≤ (0.008531985779 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12552.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12552 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12552 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12552 := gPlus_lower 12552
end BstLean.Part269.N12552

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12552
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036021576989 : ℝ) ≤ wn 12552 := by
  have hn : √(12552 : ℝ) ≤ 112.035708593288 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12552 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.035708593288 ≤ 2 / √(12552 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254903032 : ℝ) ≤ rhoBar 12552 BstLean.Part154.csC ∧
    rhoBar 12552 BstLean.Part154.csC ≤ 0.000254903426 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036021576989 : ℝ) / (1.295212 * 12552) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036021576990 : ℝ) / (1.29521 * 12552) := by gcongr
      _ ≤ (0.000254903426 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12552 BstLean.Part154.csC) ≤ 0.001019678680 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12552 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) ≤ 0.000194697065 ∧
    cc1 (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) ≤ 0.000123887013 ∧
    cc2 (rhoBar 12552 BstLean.Part154.csC) ≤ 0.000071917333 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12552 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12552 BstLean.Part154.csC * nuR (rhoBar 12552 BstLean.Part154.csC)) ≤ 0.000509823096 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254903426 : ℝ) * 0.001019678680 := by gcongr
      _ ≤ (0.000509823096 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12552 BstLean.Part154.csC) * nuR (rhoBar 12552 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019678680 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12552 BstLean.Part154.csC) * rhoBar 12552 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254903426 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254903426 / 2 + 0.399 * 0.001019678680 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194697065 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509823096 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123887013 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254903426 / 1.414213562 := by gcongr
      _ ≤ (0.000071917333 : ℝ) := by norm_num

end BstLean.Part269.N12552

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12552
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) ≤ 1.63702E-7 := by
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12552 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12552 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194697065 : ℝ) ^ 2 + 0.000123887013 ^ 2 + 3 * 0.000071917333 ^ 2 +
        2 * 0.797885 * 0.000194697065 * 0.000123887013 + 2 * 0.000194697065 * 0.000071917333 +
        4 * 0.797885 * 0.000123887013 * 0.000071917333 := by gcongr
    _ ≤ (1.63702E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12552 BstLean.Part154.csC Θ ≤ 0.002661385436 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12552 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12552 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036021576990 * 1.63702E-7 / (0.000254903032 : ℝ) := by gcongr
    _ ≤ 0.002661385436 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12552 BstLean.Part154.csC Θ ≤ 0.002953554238 + 0.000672488215 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12552 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036021576990 : ℝ) * ((2 * Θ * 0.000254903426 +
        (6863 / 10000) * 0.000254903426 * 12552 * 0.001019678680) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002953554238 + 0.000672488215 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12552 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12552 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12552 0.011 Θ ∧ gammaRatio 12552 0.011 Θ ≤ 0.000087629207 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12552 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036021576990 : ℝ) * 0.525 / ((1 - 0.011) * 12552) := by gcongr
      _ ≤ (0.000087629207 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12552 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12552 0.011 Θ) :=
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
    badAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12552 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12552 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12552 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12552 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12552 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12552 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12552 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12552 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12552 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12552 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036021576990 : ℝ) * 12552 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697294978 + 0.003333873651 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12552

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12552
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12552 BstLean.Part154.csC) (piBar (rhoBar 12552 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12552 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12552 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12552 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12552 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12552 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12552 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12552 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12552 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12552 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052796191007 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12552) ≤ 0.010659437032 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12552 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036021576990)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010659437032 + 2 * 0.737676 / 12552) := by gcongr
    _ ≤ (0.052796191007 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12552 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12552

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12552
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496796375 : ℝ) ≤ plow 12552 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12552) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954178645)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397227354) : eMP 12552 0.011 xi bn ≤ 0.001202680484 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12552 : ℝ) * (1 - 0.011))) ≤ 0.000594639684 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397227354 / (12552 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594639684 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594639684 : ℝ) + 3.141593 * 0.052954178645 / (12552 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202680484 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954178645)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397227354) : PiBarMP 12552 12 0.011 xi bn ≤ 0.162208711667 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12552 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037379504465 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.417808271389 : ℝ) ≤ √((12552 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.035708593287 : ℝ) ≤ √(12552 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12552) ≤ 0.124356854058 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037379504465 + 0.052954178645 * 1.772454 / (2 * (111.417808271389 : ℝ))) * (1 + 0.001202680484) +
        8 / (12552 * 112.035708593287) + 0.124356854058 := by gcongr
    _ ≤ (0.162208711667 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954178645)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397227354) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282913940529) :
    parallelOracle 12552 0.011 xi bn cd ≤ 0.163211419594 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12552 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12552 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496796375 : ℝ) ≤ plow 12552 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.035708593287 : ℝ) ≤ √(12552 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282913940529 : ℝ) / (2 * 0.560496796375 * 112.035708593287)) * 0.162208711667 +
        0.282913940529 ^ 2 / (2 * 0.560496796375 * 112.035708593287) := by gcongr
    _ ≤ (0.163211419594 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052954178645) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397227354)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282913940529) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12552 12552 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496796375 : ℝ) ≤ plow 12552 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.035708593287 : ℝ) ≤ √(12552 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12552 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12552 Θ 1.22 ≤ 0.011836409273 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.035708593287 := by gcongr <;> linarith
      _ ≤ (0.011836409273 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12552 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12552 12552 0.011 ≤ 0.008531985779 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12552 12552 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12552 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12552 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12552 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12552 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163211419594 + 0.011836409273 + (0.008531985779 : ℝ) *
        (1 + 2 * (0.282913940529 + 0.011836409273) / (0.560496796375 * 112.035708593287))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12552]

end BstLean.Part269.N12552

/-! The original eight local profiles supply actual 12552 moment certificates. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12552 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052954178645 ∧
    0 ≤ bN 12552 BstLean.Part154.csC (groupTheta g) ∧ bN 12552 BstLean.Part154.csC (groupTheta g) ≤ 0.001397227354 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12552 12552 0.011
      (momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12552 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12552 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12552 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230117749522 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12552 0.011
      (momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12552 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12552
/-! The actual computed-centre upper energy formula at 12552. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12552

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12552)
open BstLean.Part268 (cell12552)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085934361837
  | 2 => 0.086885560793
  | 3 => 0.087836178281
  | 4 => 0.088787923507
  | 5 => 0.089742853633
  | 6 => 0.090703424115
  | 7 => 0.091672543524
  | 8 => 0.092653632867
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12552 12552 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12552 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12552

/-! Actual upper energy certificates on all 43 source endpoints at 12552. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12552)
open BstLean.Part268 (cell12552)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12552 (gMinus 12552) (1 - (cell12552 i).lower) ≤ 1 ∧
    energyUpper 12552 (gMinus 12552) (BstLean.Part211.gPlus 12552)
      (finiteEnergy 12552 12552 0.011) (1 - (cell12552 i).lower) ≤
      (cell12552 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨10,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨11,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨12,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨13,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨14,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨15,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨16,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨17,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨18,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨19,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨20,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨21,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨22,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨23,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨24,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨25,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨26,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨27,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨28,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨29,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨30,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨31,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨32,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨33,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨34,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨35,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨36,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨37,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨38,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨39,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨40,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨41,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨42,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨43,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨44,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨45,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨46,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨47,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨48,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨49,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨50,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨51,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12552) (by norm_num)
        (q := 1 - (cell12552 ⟨52,by decide⟩).lower)
        (by norm_num [cell12552]) (by norm_num [cell12552])
      exact ⟨E.1,E.2.trans (by norm_num [cell12552])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12552

/-! Source-cell containment and simple scalar guards at 12552. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12552)
open BstLean.Part268 (cell12552)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12552 ⟨10,by decide⟩).lower ∧ (cell12552 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12552 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12552 ⟨11,by decide⟩).lower ∧ (cell12552 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12552 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12552 ⟨12,by decide⟩).lower ∧ (cell12552 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12552 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12552 ⟨13,by decide⟩).lower ∧ (cell12552 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12552 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12552 ⟨14,by decide⟩).lower ∧ (cell12552 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12552 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12552 ⟨15,by decide⟩).lower ∧ (cell12552 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12552 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12552 ⟨16,by decide⟩).lower ∧ (cell12552 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12552 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12552 ⟨17,by decide⟩).lower ∧ (cell12552 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12552 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12552 ⟨18,by decide⟩).lower ∧ (cell12552 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12552 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12552 ⟨19,by decide⟩).lower ∧ (cell12552 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12552 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12552 ⟨20,by decide⟩).lower ∧ (cell12552 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12552 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12552 ⟨21,by decide⟩).lower ∧ (cell12552 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12552 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12552 ⟨22,by decide⟩).lower ∧ (cell12552 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12552 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12552 ⟨23,by decide⟩).lower ∧ (cell12552 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12552 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12552 ⟨24,by decide⟩).lower ∧ (cell12552 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12552 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12552 ⟨25,by decide⟩).lower ∧ (cell12552 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12552 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12552 ⟨26,by decide⟩).lower ∧ (cell12552 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12552 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12552 ⟨27,by decide⟩).lower ∧ (cell12552 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12552 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12552 ⟨28,by decide⟩).lower ∧ (cell12552 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12552 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12552 ⟨29,by decide⟩).lower ∧ (cell12552 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12552 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12552 ⟨30,by decide⟩).lower ∧ (cell12552 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12552 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12552 ⟨31,by decide⟩).lower ∧ (cell12552 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12552 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12552 ⟨32,by decide⟩).lower ∧ (cell12552 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12552 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12552 ⟨33,by decide⟩).lower ∧ (cell12552 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12552 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12552 ⟨34,by decide⟩).lower ∧ (cell12552 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12552 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12552 ⟨35,by decide⟩).lower ∧ (cell12552 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12552 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12552 ⟨36,by decide⟩).lower ∧ (cell12552 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12552 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12552 ⟨37,by decide⟩).lower ∧ (cell12552 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12552 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12552 ⟨38,by decide⟩).lower ∧ (cell12552 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12552 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12552 ⟨39,by decide⟩).lower ∧ (cell12552 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12552 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12552 ⟨40,by decide⟩).lower ∧ (cell12552 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12552 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12552 ⟨41,by decide⟩).lower ∧ (cell12552 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12552 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12552 ⟨42,by decide⟩).lower ∧ (cell12552 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12552 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12552 ⟨43,by decide⟩).lower ∧ (cell12552 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12552 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12552 ⟨44,by decide⟩).lower ∧ (cell12552 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12552 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12552 ⟨45,by decide⟩).lower ∧ (cell12552 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12552 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12552 ⟨46,by decide⟩).lower ∧ (cell12552 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12552 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12552 ⟨47,by decide⟩).lower ∧ (cell12552 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12552 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12552 ⟨48,by decide⟩).lower ∧ (cell12552 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12552 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12552 ⟨49,by decide⟩).lower ∧ (cell12552 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12552 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12552 ⟨50,by decide⟩).lower ∧ (cell12552 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12552 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12552 ⟨51,by decide⟩).lower ∧ (cell12552 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12552 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12552 ⟨52,by decide⟩).lower ∧ (cell12552 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12552 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12552 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12552 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12552,cell12552,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12552 i).lower ∧
    (cell12552 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12552 i).upper ≤ (0.532 : ℝ) ∧
    (cell12552 i).centre ≤ (0.1 : ℝ) ∧ (cell12552 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12552 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12552 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12552

/-! The local source numeric instances at 12552 have no network premises. -/
namespace BstLean.Part269.N12552
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12552)
open BstLean.Part268 (cell12552)

noncomputable def sourceNumerics12552 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12552 (cell12552 i)
      scalarRow12552.M scalarRow12552.H scalarRow12552.xi := by
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
    energy_allowance := scalarRow12552.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12552]
    centre_nonneg := (scalarRow12552.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12552])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12552
/-! Actual 12553 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12553 ≤ (1.036020129489 : ℝ) := by
  have hr : (112.040171367237 : ℝ) ≤ √(12553 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.040171367237 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12553 12553 (11 / 1000) ≤
    (0.008531645931 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12553) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.040171367237 : ℝ) ≤ √(12553 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12553)
  have hdiv : K / √(12553 : ℝ) ≤ K / 112.040171367237 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.040171367237 ≤ (0.008531645931 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12553.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12553 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12553 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12553 := gPlus_lower 12553
end BstLean.Part269.N12553

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12553
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036020129488 : ℝ) ≤ wn 12553 := by
  have hn : √(12553 : ℝ) ≤ 112.040171367238 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12553 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.040171367238 ≤ 2 / √(12553 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254882369 : ℝ) ≤ rhoBar 12553 BstLean.Part154.csC ∧
    rhoBar 12553 BstLean.Part154.csC ≤ 0.000254882764 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036020129488 : ℝ) / (1.295212 * 12553) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036020129489 : ℝ) / (1.29521 * 12553) := by gcongr
      _ ≤ (0.000254882764 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12553 BstLean.Part154.csC) ≤ 0.001019596022 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12553 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) ≤ 0.000194681283 ∧
    cc1 (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) ≤ 0.000123876971 ∧
    cc2 (rhoBar 12553 BstLean.Part154.csC) ≤ 0.000071911504 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12553 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12553 BstLean.Part154.csC * nuR (rhoBar 12553 BstLean.Part154.csC)) ≤ 0.000509781770 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254882764 : ℝ) * 0.001019596022 := by gcongr
      _ ≤ (0.000509781770 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12553 BstLean.Part154.csC) * nuR (rhoBar 12553 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019596022 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12553 BstLean.Part154.csC) * rhoBar 12553 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254882764 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254882764 / 2 + 0.399 * 0.001019596022 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194681283 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509781770 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123876971 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254882764 / 1.414213562 := by gcongr
      _ ≤ (0.000071911504 : ℝ) := by norm_num

end BstLean.Part269.N12553

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12553
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) ≤ 1.63675E-7 := by
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12553 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12553 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194681283 : ℝ) ^ 2 + 0.000123876971 ^ 2 + 3 * 0.000071911504 ^ 2 +
        2 * 0.797885 * 0.000194681283 * 0.000123876971 + 2 * 0.000194681283 * 0.000071911504 +
        4 * 0.797885 * 0.000123876971 * 0.000071911504 := by gcongr
    _ ≤ (1.63675E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12553 BstLean.Part154.csC Θ ≤ 0.002661158485 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12553 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12553 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036020129489 * 1.63675E-7 / (0.000254882369 : ℝ) := by gcongr
    _ ≤ 0.002661158485 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12553 BstLean.Part154.csC Θ ≤ 0.002953306566 + 0.000672432765 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12553 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036020129489 : ℝ) * ((2 * Θ * 0.000254882764 +
        (6863 / 10000) * 0.000254882764 * 12553 * 0.001019596022) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002953306566 + 0.000672432765 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12553 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12553 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12553 0.011 Θ ∧ gammaRatio 12553 0.011 Θ ≤ 0.000087622103 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12553 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036020129489 : ℝ) * 0.525 / ((1 - 0.011) * 12553) := by gcongr
      _ ≤ (0.000087622103 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12553 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12553 0.011 Θ) :=
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
    badAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12553 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12553 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12553 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12553 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12553 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12553 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12553 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12553 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12553 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12553 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036020129489 : ℝ) * 12553 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003697047306 + 0.003333591250 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12553

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12553
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12553 BstLean.Part154.csC) (piBar (rhoBar 12553 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12553 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12553 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12553 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12553 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12553 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12553 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12553 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12553 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12553 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052794065097 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12553) ≤ 0.010659012446 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12553 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036020129489)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010659012446 + 2 * 0.737676 / 12553) := by gcongr
    _ ≤ (0.052794065097 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12553 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12553

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12553
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496842667 : ℝ) ≤ plow 12553 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12553) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953782713)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397108205) : eMP 12553 0.011 xi bn ≤ 0.001202581238 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12553 : ℝ) * (1 - 0.011))) ≤ 0.000594590645 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001397108205 / (12553 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594590645 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594590645 : ℝ) + 3.141593 * 0.052953782713 / (12553 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202581238 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953782713)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397108205) : PiBarMP 12553 12 0.011 xi bn ≤ 0.162202138189 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12553 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037377910656 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.422246432209 : ℝ) ≤ √((12553 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.040171367237 : ℝ) ≤ √(12553 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12553) ≤ 0.124351900687 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037377910656 + 0.052953782713 * 1.772454 / (2 * (111.422246432209 : ℝ))) * (1 + 0.001202581238) +
        8 / (12553 * 112.040171367237) + 0.124351900687 := by gcongr
    _ ≤ (0.162202138189 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953782713)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397108205) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282910954336) :
    parallelOracle 12553 0.011 xi bn cd ≤ 0.163204773977 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12553 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12553 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496842667 : ℝ) ≤ plow 12553 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.040171367237 : ℝ) ≤ √(12553 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282910954336 : ℝ) / (2 * 0.560496842667 * 112.040171367237)) * 0.162202138189 +
        0.282910954336 ^ 2 / (2 * 0.560496842667 * 112.040171367237) := by gcongr
    _ ≤ (0.163204773977 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953782713) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001397108205)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282910954336) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12553 12553 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496842667 : ℝ) ≤ plow 12553 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.040171367237 : ℝ) ≤ √(12553 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12553 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12553 Θ 1.22 ≤ 0.011835937806 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.040171367237 := by gcongr <;> linarith
      _ ≤ (0.011835937806 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12553 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12553 12553 0.011 ≤ 0.008531645931 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12553 12553 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12553 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12553 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12553 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12553 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163204773977 + 0.011835937806 + (0.008531645931 : ℝ) *
        (1 + 2 * (0.282910954336 + 0.011835937806) / (0.560496842667 * 112.040171367237))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12553]

end BstLean.Part269.N12553

/-! The original eight local profiles supply actual 12553 moment certificates. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12553 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052953782713 ∧
    0 ≤ bN 12553 BstLean.Part154.csC (groupTheta g) ∧ bN 12553 BstLean.Part154.csC (groupTheta g) ≤ 0.001397108205 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12553 12553 0.011
      (momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12553 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12553 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12553 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230116889239 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12553 0.011
      (momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12553 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12553
/-! The actual computed-centre upper energy formula at 12553. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12553

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12553)
open BstLean.Part268 (cell12553)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085931272921
  | 2 => 0.086882411065
  | 3 => 0.087832958226
  | 4 => 0.088784621469
  | 5 => 0.089739455446
  | 6 => 0.090699912684
  | 7 => 0.091668898371
  | 8 => 0.092649829617
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12553 12553 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12553 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12553

/-! Actual upper energy certificates on all 43 source endpoints at 12553. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12553)
open BstLean.Part268 (cell12553)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12553 (gMinus 12553) (1 - (cell12553 i).lower) ≤ 1 ∧
    energyUpper 12553 (gMinus 12553) (BstLean.Part211.gPlus 12553)
      (finiteEnergy 12553 12553 0.011) (1 - (cell12553 i).lower) ≤
      (cell12553 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨10,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨11,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨12,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨13,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨14,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨15,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨16,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨17,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨18,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨19,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨20,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨21,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨22,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨23,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨24,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨25,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨26,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨27,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨28,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨29,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨30,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨31,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨32,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨33,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨34,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨35,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨36,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨37,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨38,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨39,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨40,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨41,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨42,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨43,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨44,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨45,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨46,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨47,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨48,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨49,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨50,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨51,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12553) (by norm_num)
        (q := 1 - (cell12553 ⟨52,by decide⟩).lower)
        (by norm_num [cell12553]) (by norm_num [cell12553])
      exact ⟨E.1,E.2.trans (by norm_num [cell12553])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12553

/-! Source-cell containment and simple scalar guards at 12553. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12553)
open BstLean.Part268 (cell12553)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12553 ⟨10,by decide⟩).lower ∧ (cell12553 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12553 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12553 ⟨11,by decide⟩).lower ∧ (cell12553 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12553 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12553 ⟨12,by decide⟩).lower ∧ (cell12553 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12553 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12553 ⟨13,by decide⟩).lower ∧ (cell12553 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12553 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12553 ⟨14,by decide⟩).lower ∧ (cell12553 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12553 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12553 ⟨15,by decide⟩).lower ∧ (cell12553 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12553 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12553 ⟨16,by decide⟩).lower ∧ (cell12553 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12553 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12553 ⟨17,by decide⟩).lower ∧ (cell12553 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12553 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12553 ⟨18,by decide⟩).lower ∧ (cell12553 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12553 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12553 ⟨19,by decide⟩).lower ∧ (cell12553 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12553 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12553 ⟨20,by decide⟩).lower ∧ (cell12553 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12553 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12553 ⟨21,by decide⟩).lower ∧ (cell12553 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12553 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12553 ⟨22,by decide⟩).lower ∧ (cell12553 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12553 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12553 ⟨23,by decide⟩).lower ∧ (cell12553 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12553 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12553 ⟨24,by decide⟩).lower ∧ (cell12553 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12553 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12553 ⟨25,by decide⟩).lower ∧ (cell12553 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12553 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12553 ⟨26,by decide⟩).lower ∧ (cell12553 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12553 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12553 ⟨27,by decide⟩).lower ∧ (cell12553 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12553 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12553 ⟨28,by decide⟩).lower ∧ (cell12553 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12553 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12553 ⟨29,by decide⟩).lower ∧ (cell12553 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12553 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12553 ⟨30,by decide⟩).lower ∧ (cell12553 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12553 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12553 ⟨31,by decide⟩).lower ∧ (cell12553 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12553 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12553 ⟨32,by decide⟩).lower ∧ (cell12553 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12553 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12553 ⟨33,by decide⟩).lower ∧ (cell12553 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12553 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12553 ⟨34,by decide⟩).lower ∧ (cell12553 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12553 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12553 ⟨35,by decide⟩).lower ∧ (cell12553 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12553 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12553 ⟨36,by decide⟩).lower ∧ (cell12553 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12553 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12553 ⟨37,by decide⟩).lower ∧ (cell12553 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12553 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12553 ⟨38,by decide⟩).lower ∧ (cell12553 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12553 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12553 ⟨39,by decide⟩).lower ∧ (cell12553 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12553 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12553 ⟨40,by decide⟩).lower ∧ (cell12553 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12553 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12553 ⟨41,by decide⟩).lower ∧ (cell12553 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12553 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12553 ⟨42,by decide⟩).lower ∧ (cell12553 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12553 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12553 ⟨43,by decide⟩).lower ∧ (cell12553 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12553 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12553 ⟨44,by decide⟩).lower ∧ (cell12553 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12553 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12553 ⟨45,by decide⟩).lower ∧ (cell12553 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12553 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12553 ⟨46,by decide⟩).lower ∧ (cell12553 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12553 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12553 ⟨47,by decide⟩).lower ∧ (cell12553 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12553 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12553 ⟨48,by decide⟩).lower ∧ (cell12553 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12553 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12553 ⟨49,by decide⟩).lower ∧ (cell12553 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12553 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12553 ⟨50,by decide⟩).lower ∧ (cell12553 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12553 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12553 ⟨51,by decide⟩).lower ∧ (cell12553 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12553 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12553 ⟨52,by decide⟩).lower ∧ (cell12553 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12553 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12553 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12553 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12553,cell12553,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12553 i).lower ∧
    (cell12553 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12553 i).upper ≤ (0.532 : ℝ) ∧
    (cell12553 i).centre ≤ (0.1 : ℝ) ∧ (cell12553 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12553 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12553 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12553

/-! The local source numeric instances at 12553 have no network premises. -/
namespace BstLean.Part269.N12553
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12553)
open BstLean.Part268 (cell12553)

noncomputable def sourceNumerics12553 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12553 (cell12553 i)
      scalarRow12553.M scalarRow12553.H scalarRow12553.xi := by
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
    energy_allowance := scalarRow12553.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12553]
    centre_nonneg := (scalarRow12553.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12553])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12553
/-! Actual 12554 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12554 ≤ (1.036018682162 : ℝ) := by
  have hr : (112.044633963434 : ℝ) ≤ √(12554 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.044633963434 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12554 12554 (11 / 1000) ≤
    (0.008531306124 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12554) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.044633963434 : ℝ) ≤ √(12554 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12554)
  have hdiv : K / √(12554 : ℝ) ≤ K / 112.044633963434 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.044633963434 ≤ (0.008531306124 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12554.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12554 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12554 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12554 := gPlus_lower 12554
end BstLean.Part269.N12554

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12554
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036018682161 : ℝ) ≤ wn 12554 := by
  have hn : √(12554 : ℝ) ≤ 112.044633963435 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12554 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.044633963435 ≤ 2 / √(12554 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254861711 : ℝ) ≤ rhoBar 12554 BstLean.Part154.csC ∧
    rhoBar 12554 BstLean.Part154.csC ≤ 0.000254862105 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036018682161 : ℝ) / (1.295212 * 12554) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036018682162 : ℝ) / (1.29521 * 12554) := by gcongr
      _ ≤ (0.000254862105 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12554 BstLean.Part154.csC) ≤ 0.001019513375 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12554 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) ≤ 0.000194665502 ∧
    cc1 (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) ≤ 0.000123866930 ∧
    cc2 (rhoBar 12554 BstLean.Part154.csC) ≤ 0.000071905675 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12554 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12554 BstLean.Part154.csC * nuR (rhoBar 12554 BstLean.Part154.csC)) ≤ 0.000509740449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254862105 : ℝ) * 0.001019513375 := by gcongr
      _ ≤ (0.000509740449 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12554 BstLean.Part154.csC) * nuR (rhoBar 12554 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019513375 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12554 BstLean.Part154.csC) * rhoBar 12554 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254862105 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254862105 / 2 + 0.399 * 0.001019513375 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194665502 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509740449 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123866930 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254862105 / 1.414213562 := by gcongr
      _ ≤ (0.000071905675 : ℝ) := by norm_num

end BstLean.Part269.N12554

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12554
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) ≤ 1.63649E-7 := by
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12554 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12554 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194665502 : ℝ) ^ 2 + 0.000123866930 ^ 2 + 3 * 0.000071905675 ^ 2 +
        2 * 0.797885 * 0.000194665502 * 0.000123866930 + 2 * 0.000194665502 * 0.000071905675 +
        4 * 0.797885 * 0.000123866930 * 0.000071905675 := by gcongr
    _ ≤ (1.63649E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12554 BstLean.Part154.csC Θ ≤ 0.002660947707 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12554 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12554 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036018682162 * 1.63649E-7 / (0.000254861711 : ℝ) := by gcongr
    _ ≤ 0.002660947707 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12554 BstLean.Part154.csC Θ ≤ 0.002953058923 + 0.000672377323 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12554 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036018682162 : ℝ) * ((2 * Θ * 0.000254862105 +
        (6863 / 10000) * 0.000254862105 * 12554 * 0.001019513375) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002953058923 + 0.000672377323 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12554 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12554 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12554 0.011 Θ ∧ gammaRatio 12554 0.011 Θ ≤ 0.000087615001 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12554 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036018682162 : ℝ) * 0.525 / ((1 - 0.011) * 12554) := by gcongr
      _ ≤ (0.000087615001 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12554 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12554 0.011 Θ) :=
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
    badAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12554 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12554 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12554 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12554 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12554 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12554 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12554 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12554 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12554 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12554 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036018682162 : ℝ) * 12554 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003696799663 + 0.003333325030 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12554

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12554
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12554 BstLean.Part154.csC) (piBar (rhoBar 12554 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12554 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12554 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12554 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12554 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12554 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12554 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12554 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12554 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12554 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052791939445 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12554) ≤ 0.010658587911 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12554 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036018682162)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010658587911 + 2 * 0.737676 / 12554) := by gcongr
    _ ≤ (0.052791939445 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12554 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12554

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12554
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496888951 : ℝ) ≤ plow 12554 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12554) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953395304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396997547) : eMP 12554 0.011 xi bn ≤ 0.001202485616 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12554 : ℝ) * (1 - 0.011))) ≤ 0.000594543417 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396997547 / (12554 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594543417 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594543417 : ℝ) + 3.141593 * 0.052953395304 / (12554 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202485616 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953395304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396997547) : PiBarMP 12554 12 0.011 xi bn ≤ 0.162195679167 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12554 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037376430368 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.426684416256 : ℝ) ≤ √((12554 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.044633963434 : ℝ) ≤ √(12554 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12554) ≤ 0.124346947908 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037376430368 + 0.052953395304 * 1.772454 / (2 * (111.426684416256 : ℝ))) * (1 + 0.001202485616) +
        8 / (12554 * 112.044633963434) + 0.124346947908 := by gcongr
    _ ≤ (0.162195679167 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953395304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396997547) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282907986917) :
    parallelOracle 12554 0.011 xi bn cd ≤ 0.163198243190 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12554 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12554 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496888951 : ℝ) ≤ plow 12554 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.044633963434 : ℝ) ≤ √(12554 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282907986917 : ℝ) / (2 * 0.560496888951 * 112.044633963434)) * 0.162195679167 +
        0.282907986917 ^ 2 / (2 * 0.560496888951 * 112.044633963434) := by gcongr
    _ ≤ (0.163198243190 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052953395304) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396997547)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282907986917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12554 12554 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496888951 : ℝ) ≤ plow 12554 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.044633963434 : ℝ) ≤ √(12554 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12554 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12554 Θ 1.22 ≤ 0.011835466395 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.044633963434 := by gcongr <;> linarith
      _ ≤ (0.011835466395 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12554 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12554 12554 0.011 ≤ 0.008531306124 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12554 12554 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12554 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12554 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12554 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12554 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163198243190 + 0.011835466395 + (0.008531306124 : ℝ) *
        (1 + 2 * (0.282907986917 + 0.011835466395) / (0.560496888951 * 112.044633963434))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12554]

end BstLean.Part269.N12554

/-! The original eight local profiles supply actual 12554 moment certificates. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12554 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052953395304 ∧
    0 ≤ bN 12554 BstLean.Part154.csC (groupTheta g) ∧ bN 12554 BstLean.Part154.csC (groupTheta g) ≤ 0.001396997547 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12554 12554 0.011
      (momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12554 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12554 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12554 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230116047472 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12554 0.011
      (momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12554 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12554
/-! The actual computed-centre upper energy formula at 12554. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12554

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12554)
open BstLean.Part268 (cell12554)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085928185267
  | 2 => 0.086879262651
  | 3 => 0.087829739552
  | 4 => 0.088781320895
  | 5 => 0.089736058822
  | 6 => 0.090696402938
  | 7 => 0.091665255048
  | 8 => 0.092646028373
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12554 12554 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12554 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12554

/-! Actual upper energy certificates on all 43 source endpoints at 12554. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12554)
open BstLean.Part268 (cell12554)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12554 (gMinus 12554) (1 - (cell12554 i).lower) ≤ 1 ∧
    energyUpper 12554 (gMinus 12554) (BstLean.Part211.gPlus 12554)
      (finiteEnergy 12554 12554 0.011) (1 - (cell12554 i).lower) ≤
      (cell12554 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨10,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨11,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨12,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨13,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨14,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨15,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨16,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨17,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨18,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨19,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨20,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨21,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨22,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨23,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨24,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨25,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨26,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨27,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨28,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨29,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨30,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨31,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨32,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨33,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨34,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨35,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨36,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨37,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨38,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨39,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨40,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨41,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨42,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨43,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨44,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨45,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨46,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨47,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨48,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨49,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨50,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨51,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12554) (by norm_num)
        (q := 1 - (cell12554 ⟨52,by decide⟩).lower)
        (by norm_num [cell12554]) (by norm_num [cell12554])
      exact ⟨E.1,E.2.trans (by norm_num [cell12554])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12554

/-! Source-cell containment and simple scalar guards at 12554. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12554)
open BstLean.Part268 (cell12554)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12554 ⟨10,by decide⟩).lower ∧ (cell12554 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12554 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12554 ⟨11,by decide⟩).lower ∧ (cell12554 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12554 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12554 ⟨12,by decide⟩).lower ∧ (cell12554 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12554 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12554 ⟨13,by decide⟩).lower ∧ (cell12554 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12554 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12554 ⟨14,by decide⟩).lower ∧ (cell12554 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12554 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12554 ⟨15,by decide⟩).lower ∧ (cell12554 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12554 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12554 ⟨16,by decide⟩).lower ∧ (cell12554 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12554 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12554 ⟨17,by decide⟩).lower ∧ (cell12554 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12554 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12554 ⟨18,by decide⟩).lower ∧ (cell12554 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12554 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12554 ⟨19,by decide⟩).lower ∧ (cell12554 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12554 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12554 ⟨20,by decide⟩).lower ∧ (cell12554 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12554 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12554 ⟨21,by decide⟩).lower ∧ (cell12554 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12554 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12554 ⟨22,by decide⟩).lower ∧ (cell12554 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12554 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12554 ⟨23,by decide⟩).lower ∧ (cell12554 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12554 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12554 ⟨24,by decide⟩).lower ∧ (cell12554 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12554 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12554 ⟨25,by decide⟩).lower ∧ (cell12554 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12554 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12554 ⟨26,by decide⟩).lower ∧ (cell12554 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12554 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12554 ⟨27,by decide⟩).lower ∧ (cell12554 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12554 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12554 ⟨28,by decide⟩).lower ∧ (cell12554 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12554 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12554 ⟨29,by decide⟩).lower ∧ (cell12554 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12554 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12554 ⟨30,by decide⟩).lower ∧ (cell12554 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12554 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12554 ⟨31,by decide⟩).lower ∧ (cell12554 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12554 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12554 ⟨32,by decide⟩).lower ∧ (cell12554 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12554 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12554 ⟨33,by decide⟩).lower ∧ (cell12554 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12554 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12554 ⟨34,by decide⟩).lower ∧ (cell12554 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12554 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12554 ⟨35,by decide⟩).lower ∧ (cell12554 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12554 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12554 ⟨36,by decide⟩).lower ∧ (cell12554 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12554 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12554 ⟨37,by decide⟩).lower ∧ (cell12554 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12554 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12554 ⟨38,by decide⟩).lower ∧ (cell12554 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12554 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12554 ⟨39,by decide⟩).lower ∧ (cell12554 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12554 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12554 ⟨40,by decide⟩).lower ∧ (cell12554 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12554 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12554 ⟨41,by decide⟩).lower ∧ (cell12554 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12554 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12554 ⟨42,by decide⟩).lower ∧ (cell12554 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12554 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12554 ⟨43,by decide⟩).lower ∧ (cell12554 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12554 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12554 ⟨44,by decide⟩).lower ∧ (cell12554 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12554 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12554 ⟨45,by decide⟩).lower ∧ (cell12554 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12554 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12554 ⟨46,by decide⟩).lower ∧ (cell12554 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12554 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12554 ⟨47,by decide⟩).lower ∧ (cell12554 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12554 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12554 ⟨48,by decide⟩).lower ∧ (cell12554 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12554 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12554 ⟨49,by decide⟩).lower ∧ (cell12554 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12554 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12554 ⟨50,by decide⟩).lower ∧ (cell12554 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12554 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12554 ⟨51,by decide⟩).lower ∧ (cell12554 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12554 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12554 ⟨52,by decide⟩).lower ∧ (cell12554 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12554 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12554 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12554 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12554,cell12554,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12554 i).lower ∧
    (cell12554 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12554 i).upper ≤ (0.532 : ℝ) ∧
    (cell12554 i).centre ≤ (0.1 : ℝ) ∧ (cell12554 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12554 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12554 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12554

/-! The local source numeric instances at 12554 have no network premises. -/
namespace BstLean.Part269.N12554
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12554)
open BstLean.Part268 (cell12554)

noncomputable def sourceNumerics12554 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12554 (cell12554 i)
      scalarRow12554.M scalarRow12554.H scalarRow12554.xi := by
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
    energy_allowance := scalarRow12554.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12554]
    centre_nonneg := (scalarRow12554.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12554])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12554
/-! Actual 12555 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12555 ≤ (1.036017235009 : ℝ) := by
  have hr : (112.049096381898 : ℝ) ≤ √(12555 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.049096381898 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12555 12555 (11 / 1000) ≤
    (0.008530966357 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12555) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.049096381898 : ℝ) ≤ √(12555 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12555)
  have hdiv : K / √(12555 : ℝ) ≤ K / 112.049096381898 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.049096381898 ≤ (0.008530966357 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12555.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12555 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12555 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12555 := gPlus_lower 12555
end BstLean.Part269.N12555

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12555
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036017235008 : ℝ) ≤ wn 12555 := by
  have hn : √(12555 : ℝ) ≤ 112.049096381899 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12555 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.049096381899 ≤ 2 / √(12555 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254841055 : ℝ) ≤ rhoBar 12555 BstLean.Part154.csC ∧
    rhoBar 12555 BstLean.Part154.csC ≤ 0.000254841449 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036017235008 : ℝ) / (1.295212 * 12555) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036017235009 : ℝ) / (1.29521 * 12555) := by gcongr
      _ ≤ (0.000254841449 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12555 BstLean.Part154.csC) ≤ 0.001019430741 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12555 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) ≤ 0.000194649724 ∧
    cc1 (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) ≤ 0.000123856890 ∧
    cc2 (rhoBar 12555 BstLean.Part154.csC) ≤ 0.000071899847 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12555 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12555 BstLean.Part154.csC * nuR (rhoBar 12555 BstLean.Part154.csC)) ≤ 0.000509699134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254841449 : ℝ) * 0.001019430741 := by gcongr
      _ ≤ (0.000509699134 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12555 BstLean.Part154.csC) * nuR (rhoBar 12555 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019430741 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12555 BstLean.Part154.csC) * rhoBar 12555 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254841449 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254841449 / 2 + 0.399 * 0.001019430741 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194649724 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509699134 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123856890 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254841449 / 1.414213562 := by gcongr
      _ ≤ (0.000071899847 : ℝ) := by norm_num

end BstLean.Part269.N12555

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12555
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) ≤ 1.63622E-7 := by
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12555 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12555 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194649724 : ℝ) ^ 2 + 0.000123856890 ^ 2 + 3 * 0.000071899847 ^ 2 +
        2 * 0.797885 * 0.000194649724 * 0.000123856890 + 2 * 0.000194649724 * 0.000071899847 +
        4 * 0.797885 * 0.000123856890 * 0.000071899847 := by gcongr
    _ ≤ (1.63622E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12555 BstLean.Part154.csC Θ ≤ 0.002660720614 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12555 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12555 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036017235009 * 1.63622E-7 / (0.000254841055 : ℝ) := by gcongr
    _ ≤ 0.002660720614 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12555 BstLean.Part154.csC Θ ≤ 0.002952811317 + 0.000672321889 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12555 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036017235009 : ℝ) * ((2 * Θ * 0.000254841449 +
        (6863 / 10000) * 0.000254841449 * 12555 * 0.001019430741) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002952811317 + 0.000672321889 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12555 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12555 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12555 0.011 Θ ∧ gammaRatio 12555 0.011 Θ ≤ 0.000087607901 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12555 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036017235009 : ℝ) * 0.525 / ((1 - 0.011) * 12555) := by gcongr
      _ ≤ (0.000087607901 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12555 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12555 0.011 Θ) :=
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
    badAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12555 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12555 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12555 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12555 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12555 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12555 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12555 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12555 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12555 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12555 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036017235009 : ℝ) * 12555 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003696552057 + 0.003333042503 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12555

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12555
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12555 BstLean.Part154.csC) (piBar (rhoBar 12555 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12555 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12555 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12555 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12555 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12555 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12555 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12555 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12555 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12555 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052789814049 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12555) ≤ 0.010658163427 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12555 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036017235009)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010658163427 + 2 * 0.737676 / 12555) := by gcongr
    _ ≤ (0.052789814049 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12555 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12555

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12555
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496935228 : ℝ) ≤ plow 12555 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12555) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952999372)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396878323) : eMP 12555 0.011 xi bn ≤ 0.001202386353 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12555 : ℝ) * (1 - 0.011))) ≤ 0.000594494369 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396878323 / (12555 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594494369 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594494369 : ℝ) + 3.141593 * 0.052952999372 / (12555 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202386353 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952999372)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396878323) : PiBarMP 12555 12 0.011 xi bn ≤ 0.162189105742 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12555 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037374835425 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.431122223551 : ℝ) ≤ √((12555 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.049096381898 : ℝ) ≤ √(12555 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12555) ≤ 0.124341995721 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037374835425 + 0.052952999372 * 1.772454 / (2 * (111.431122223551 : ℝ))) * (1 + 0.001202386353) +
        8 / (12555 * 112.049096381898) + 0.124341995721 := by gcongr
    _ ≤ (0.162189105742 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952999372)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396878323) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282905001232) :
    parallelOracle 12555 0.011 xi bn cd ≤ 0.163191597644 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12555 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12555 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496935228 : ℝ) ≤ plow 12555 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.049096381898 : ℝ) ≤ √(12555 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282905001232 : ℝ) / (2 * 0.560496935228 * 112.049096381898)) * 0.162189105742 +
        0.282905001232 ^ 2 / (2 * 0.560496935228 * 112.049096381898) := by gcongr
    _ ≤ (0.163191597644 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952999372) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396878323)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282905001232) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12555 12555 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496935228 : ℝ) ≤ plow 12555 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.049096381898 : ℝ) ≤ √(12555 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12555 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12555 Θ 1.22 ≤ 0.011834995041 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.049096381898 := by gcongr <;> linarith
      _ ≤ (0.011834995041 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12555 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12555 12555 0.011 ≤ 0.008530966357 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12555 12555 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12555 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12555 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12555 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12555 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163191597644 + 0.011834995041 + (0.008530966357 : ℝ) *
        (1 + 2 * (0.282905001232 + 0.011834995041) / (0.560496935228 * 112.049096381898))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12555]

end BstLean.Part269.N12555

/-! The original eight local profiles supply actual 12555 moment certificates. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12555 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052952999372 ∧
    0 ≤ bN 12555 BstLean.Part154.csC (groupTheta g) ∧ bN 12555 BstLean.Part154.csC (groupTheta g) ≤ 0.001396878323 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12555 12555 0.011
      (momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12555 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12555 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12555 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230115187183 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12555 0.011
      (momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12555 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12555
/-! The actual computed-centre upper energy formula at 12555. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12555

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12555)
open BstLean.Part268 (cell12555)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085925098873
  | 2 => 0.086876115552
  | 3 => 0.087826522260
  | 4 => 0.088778021784
  | 5 => 0.089732663760
  | 6 => 0.090692894875
  | 7 => 0.091661613554
  | 8 => 0.092642229132
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12555 12555 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12555 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12555

/-! Actual upper energy certificates on all 43 source endpoints at 12555. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12555)
open BstLean.Part268 (cell12555)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12555 (gMinus 12555) (1 - (cell12555 i).lower) ≤ 1 ∧
    energyUpper 12555 (gMinus 12555) (BstLean.Part211.gPlus 12555)
      (finiteEnergy 12555 12555 0.011) (1 - (cell12555 i).lower) ≤
      (cell12555 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨10,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨11,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨12,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨13,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨14,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨15,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨16,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨17,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨18,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨19,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨20,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨21,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨22,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨23,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨24,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨25,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨26,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨27,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨28,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨29,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨30,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨31,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨32,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨33,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨34,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨35,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨36,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨37,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨38,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨39,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨40,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨41,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨42,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨43,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨44,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨45,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨46,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨47,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨48,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨49,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨50,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨51,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12555) (by norm_num)
        (q := 1 - (cell12555 ⟨52,by decide⟩).lower)
        (by norm_num [cell12555]) (by norm_num [cell12555])
      exact ⟨E.1,E.2.trans (by norm_num [cell12555])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12555

/-! Source-cell containment and simple scalar guards at 12555. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12555)
open BstLean.Part268 (cell12555)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12555 ⟨10,by decide⟩).lower ∧ (cell12555 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12555 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12555 ⟨11,by decide⟩).lower ∧ (cell12555 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12555 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12555 ⟨12,by decide⟩).lower ∧ (cell12555 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12555 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12555 ⟨13,by decide⟩).lower ∧ (cell12555 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12555 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12555 ⟨14,by decide⟩).lower ∧ (cell12555 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12555 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12555 ⟨15,by decide⟩).lower ∧ (cell12555 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12555 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12555 ⟨16,by decide⟩).lower ∧ (cell12555 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12555 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12555 ⟨17,by decide⟩).lower ∧ (cell12555 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12555 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12555 ⟨18,by decide⟩).lower ∧ (cell12555 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12555 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12555 ⟨19,by decide⟩).lower ∧ (cell12555 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12555 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12555 ⟨20,by decide⟩).lower ∧ (cell12555 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12555 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12555 ⟨21,by decide⟩).lower ∧ (cell12555 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12555 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12555 ⟨22,by decide⟩).lower ∧ (cell12555 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12555 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12555 ⟨23,by decide⟩).lower ∧ (cell12555 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12555 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12555 ⟨24,by decide⟩).lower ∧ (cell12555 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12555 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12555 ⟨25,by decide⟩).lower ∧ (cell12555 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12555 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12555 ⟨26,by decide⟩).lower ∧ (cell12555 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12555 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12555 ⟨27,by decide⟩).lower ∧ (cell12555 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12555 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12555 ⟨28,by decide⟩).lower ∧ (cell12555 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12555 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12555 ⟨29,by decide⟩).lower ∧ (cell12555 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12555 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12555 ⟨30,by decide⟩).lower ∧ (cell12555 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12555 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12555 ⟨31,by decide⟩).lower ∧ (cell12555 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12555 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12555 ⟨32,by decide⟩).lower ∧ (cell12555 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12555 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12555 ⟨33,by decide⟩).lower ∧ (cell12555 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12555 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12555 ⟨34,by decide⟩).lower ∧ (cell12555 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12555 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12555 ⟨35,by decide⟩).lower ∧ (cell12555 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12555 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12555 ⟨36,by decide⟩).lower ∧ (cell12555 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12555 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12555 ⟨37,by decide⟩).lower ∧ (cell12555 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12555 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12555 ⟨38,by decide⟩).lower ∧ (cell12555 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12555 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12555 ⟨39,by decide⟩).lower ∧ (cell12555 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12555 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12555 ⟨40,by decide⟩).lower ∧ (cell12555 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12555 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12555 ⟨41,by decide⟩).lower ∧ (cell12555 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12555 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12555 ⟨42,by decide⟩).lower ∧ (cell12555 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12555 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12555 ⟨43,by decide⟩).lower ∧ (cell12555 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12555 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12555 ⟨44,by decide⟩).lower ∧ (cell12555 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12555 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12555 ⟨45,by decide⟩).lower ∧ (cell12555 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12555 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12555 ⟨46,by decide⟩).lower ∧ (cell12555 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12555 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12555 ⟨47,by decide⟩).lower ∧ (cell12555 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12555 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12555 ⟨48,by decide⟩).lower ∧ (cell12555 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12555 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12555 ⟨49,by decide⟩).lower ∧ (cell12555 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12555 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12555 ⟨50,by decide⟩).lower ∧ (cell12555 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12555 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12555 ⟨51,by decide⟩).lower ∧ (cell12555 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12555 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12555 ⟨52,by decide⟩).lower ∧ (cell12555 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12555 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12555 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12555 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12555,cell12555,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12555 i).lower ∧
    (cell12555 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12555 i).upper ≤ (0.532 : ℝ) ∧
    (cell12555 i).centre ≤ (0.1 : ℝ) ∧ (cell12555 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12555 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12555 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12555

/-! The local source numeric instances at 12555 have no network premises. -/
namespace BstLean.Part269.N12555
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12555)
open BstLean.Part268 (cell12555)

noncomputable def sourceNumerics12555 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12555 (cell12555 i)
      scalarRow12555.M scalarRow12555.H scalarRow12555.xi := by
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
    energy_allowance := scalarRow12555.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12555]
    centre_nonneg := (scalarRow12555.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12555])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12555
/-! Actual 12556 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12556 ≤ (1.036015788029 : ℝ) := by
  have hr : (112.053558622651 : ℝ) ≤ √(12556 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.053558622651 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12556 12556 (11 / 1000) ≤
    (0.008530626631 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12556) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.053558622651 : ℝ) ≤ √(12556 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12556)
  have hdiv : K / √(12556 : ℝ) ≤ K / 112.053558622651 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.053558622651 ≤ (0.008530626631 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12556.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12556 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12556 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12556 := gPlus_lower 12556
end BstLean.Part269.N12556

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12556
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036015788028 : ℝ) ≤ wn 12556 := by
  have hn : √(12556 : ℝ) ≤ 112.053558622652 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12556 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.053558622652 ≤ 2 / √(12556 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254820403 : ℝ) ≤ rhoBar 12556 BstLean.Part154.csC ∧
    rhoBar 12556 BstLean.Part154.csC ≤ 0.000254820797 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036015788028 : ℝ) / (1.295212 * 12556) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036015788029 : ℝ) / (1.29521 * 12556) := by gcongr
      _ ≤ (0.000254820797 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12556 BstLean.Part154.csC) ≤ 0.001019348122 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12556 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) ≤ 0.000194633949 ∧
    cc1 (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) ≤ 0.000123846853 ∧
    cc2 (rhoBar 12556 BstLean.Part154.csC) ≤ 0.000071894020 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12556 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12556 BstLean.Part154.csC * nuR (rhoBar 12556 BstLean.Part154.csC)) ≤ 0.000509657828 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254820797 : ℝ) * 0.001019348122 := by gcongr
      _ ≤ (0.000509657828 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12556 BstLean.Part154.csC) * nuR (rhoBar 12556 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019348122 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12556 BstLean.Part154.csC) * rhoBar 12556 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254820797 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254820797 / 2 + 0.399 * 0.001019348122 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194633949 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509657828 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123846853 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254820797 / 1.414213562 := by gcongr
      _ ≤ (0.000071894020 : ℝ) := by norm_num

end BstLean.Part269.N12556

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12556
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) ≤ 1.63596E-7 := by
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12556 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12556 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194633949 : ℝ) ^ 2 + 0.000123846853 ^ 2 + 3 * 0.000071894020 ^ 2 +
        2 * 0.797885 * 0.000194633949 * 0.000123846853 + 2 * 0.000194633949 * 0.000071894020 +
        4 * 0.797885 * 0.000123846853 * 0.000071894020 := by gcongr
    _ ≤ (1.63596E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12556 BstLean.Part154.csC Θ ≤ 0.002660509706 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12556 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12556 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036015788029 * 1.63596E-7 / (0.000254820403 : ℝ) := by gcongr
    _ ≤ 0.002660509706 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12556 BstLean.Part154.csC Θ ≤ 0.002952563765 + 0.000672266466 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12556 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036015788029 : ℝ) * ((2 * Θ * 0.000254820797 +
        (6863 / 10000) * 0.000254820797 * 12556 * 0.001019348122) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002952563765 + 0.000672266466 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12556 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12556 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12556 0.011 Θ ∧ gammaRatio 12556 0.011 Θ ≤ 0.000087600801 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12556 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036015788029 : ℝ) * 0.525 / ((1 - 0.011) * 12556) := by gcongr
      _ ≤ (0.000087600801 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12556 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12556 0.011 Θ) :=
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
    badAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12556 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12556 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12556 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12556 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12556 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12556 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12556 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12556 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12556 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12556 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036015788029 : ℝ) * 12556 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003696304505 + 0.003332776172 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12556

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12556
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12556 BstLean.Part154.csC) (piBar (rhoBar 12556 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12556 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12556 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12556 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12556 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12556 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12556 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12556 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12556 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12556 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052787688911 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12556) ≤ 0.010657738994 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12556 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036015788029)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010657738994 + 2 * 0.737676 / 12556) := by gcongr
    _ ≤ (0.052787688911 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12556 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12556

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12556
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560496981498 : ℝ) ≤ plow 12556 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12556) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952611996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396767596) : eMP 12556 0.011 xi bn ≤ 0.001202290716 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12556 : ℝ) * (1 - 0.011))) ≤ 0.000594447133 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396767596 / (12556 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594447133 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594447133 : ℝ) + 3.141593 * 0.052952611996 / (12556 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202290716 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952611996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396767596) : PiBarMP 12556 12 0.011 xi bn ≤ 0.162182646862 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12556 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037373354091 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.435559854114 : ℝ) ≤ √((12556 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.053558622651 : ℝ) ≤ √(12556 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12556) ≤ 0.124337044125 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037373354091 + 0.052952611996 * 1.772454 / (2 * (111.435559854114 : ℝ))) * (1 + 0.001202290716) +
        8 / (12556 * 112.053558622651) + 0.124337044125 := by gcongr
    _ ≤ (0.162182646862 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952611996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396767596) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282902034392) :
    parallelOracle 12556 0.011 xi bn cd ≤ 0.163185067018 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12556 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12556 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560496981498 : ℝ) ≤ plow 12556 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.053558622651 : ℝ) ≤ √(12556 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282902034392 : ℝ) / (2 * 0.560496981498 * 112.053558622651)) * 0.162182646862 +
        0.282902034392 ^ 2 / (2 * 0.560496981498 * 112.053558622651) := by gcongr
    _ ≤ (0.163185067018 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952611996) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396767596)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282902034392) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12556 12556 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560496981498 : ℝ) ≤ plow 12556 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.053558622651 : ℝ) ≤ √(12556 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12556 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12556 Θ 1.22 ≤ 0.011834523743 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.053558622651 := by gcongr <;> linarith
      _ ≤ (0.011834523743 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12556 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12556 12556 0.011 ≤ 0.008530626631 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12556 12556 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12556 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12556 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12556 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12556 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163185067018 + 0.011834523743 + (0.008530626631 : ℝ) *
        (1 + 2 * (0.282902034392 + 0.011834523743) / (0.560496981498 * 112.053558622651))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12556]

end BstLean.Part269.N12556

/-! The original eight local profiles supply actual 12556 moment certificates. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12556 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052952611996 ∧
    0 ≤ bN 12556 BstLean.Part154.csC (groupTheta g) ∧ bN 12556 BstLean.Part154.csC (groupTheta g) ≤ 0.001396767596 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12556 12556 0.011
      (momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12556 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12556 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12556 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230114345481 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12556 0.011
      (momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12556 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12556
/-! The actual computed-centre upper energy formula at 12556. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12556

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12556)
open BstLean.Part268 (cell12556)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085922013738
  | 2 => 0.086872969766
  | 3 => 0.087823306347
  | 4 => 0.088774724133
  | 5 => 0.089729270257
  | 6 => 0.090689388491
  | 7 => 0.091657973886
  | 8 => 0.092638431892
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12556 12556 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12556 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12556

/-! Actual upper energy certificates on all 43 source endpoints at 12556. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12556)
open BstLean.Part268 (cell12556)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12556 (gMinus 12556) (1 - (cell12556 i).lower) ≤ 1 ∧
    energyUpper 12556 (gMinus 12556) (BstLean.Part211.gPlus 12556)
      (finiteEnergy 12556 12556 0.011) (1 - (cell12556 i).lower) ≤
      (cell12556 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨10,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨11,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨12,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨13,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨14,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨15,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨16,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨17,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨18,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨19,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨20,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨21,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨22,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨23,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨24,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨25,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨26,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨27,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨28,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨29,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨30,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨31,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨32,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨33,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨34,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨35,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨36,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨37,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨38,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨39,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨40,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨41,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨42,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨43,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨44,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨45,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨46,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨47,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨48,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨49,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨50,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨51,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12556) (by norm_num)
        (q := 1 - (cell12556 ⟨52,by decide⟩).lower)
        (by norm_num [cell12556]) (by norm_num [cell12556])
      exact ⟨E.1,E.2.trans (by norm_num [cell12556])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12556

/-! Source-cell containment and simple scalar guards at 12556. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12556)
open BstLean.Part268 (cell12556)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12556 ⟨10,by decide⟩).lower ∧ (cell12556 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12556 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12556 ⟨11,by decide⟩).lower ∧ (cell12556 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12556 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12556 ⟨12,by decide⟩).lower ∧ (cell12556 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12556 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12556 ⟨13,by decide⟩).lower ∧ (cell12556 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12556 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12556 ⟨14,by decide⟩).lower ∧ (cell12556 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12556 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12556 ⟨15,by decide⟩).lower ∧ (cell12556 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12556 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12556 ⟨16,by decide⟩).lower ∧ (cell12556 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12556 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12556 ⟨17,by decide⟩).lower ∧ (cell12556 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12556 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12556 ⟨18,by decide⟩).lower ∧ (cell12556 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12556 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12556 ⟨19,by decide⟩).lower ∧ (cell12556 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12556 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12556 ⟨20,by decide⟩).lower ∧ (cell12556 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12556 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12556 ⟨21,by decide⟩).lower ∧ (cell12556 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12556 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12556 ⟨22,by decide⟩).lower ∧ (cell12556 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12556 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12556 ⟨23,by decide⟩).lower ∧ (cell12556 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12556 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12556 ⟨24,by decide⟩).lower ∧ (cell12556 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12556 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12556 ⟨25,by decide⟩).lower ∧ (cell12556 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12556 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12556 ⟨26,by decide⟩).lower ∧ (cell12556 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12556 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12556 ⟨27,by decide⟩).lower ∧ (cell12556 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12556 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12556 ⟨28,by decide⟩).lower ∧ (cell12556 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12556 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12556 ⟨29,by decide⟩).lower ∧ (cell12556 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12556 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12556 ⟨30,by decide⟩).lower ∧ (cell12556 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12556 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12556 ⟨31,by decide⟩).lower ∧ (cell12556 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12556 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12556 ⟨32,by decide⟩).lower ∧ (cell12556 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12556 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12556 ⟨33,by decide⟩).lower ∧ (cell12556 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12556 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12556 ⟨34,by decide⟩).lower ∧ (cell12556 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12556 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12556 ⟨35,by decide⟩).lower ∧ (cell12556 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12556 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12556 ⟨36,by decide⟩).lower ∧ (cell12556 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12556 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12556 ⟨37,by decide⟩).lower ∧ (cell12556 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12556 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12556 ⟨38,by decide⟩).lower ∧ (cell12556 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12556 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12556 ⟨39,by decide⟩).lower ∧ (cell12556 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12556 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12556 ⟨40,by decide⟩).lower ∧ (cell12556 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12556 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12556 ⟨41,by decide⟩).lower ∧ (cell12556 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12556 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12556 ⟨42,by decide⟩).lower ∧ (cell12556 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12556 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12556 ⟨43,by decide⟩).lower ∧ (cell12556 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12556 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12556 ⟨44,by decide⟩).lower ∧ (cell12556 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12556 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12556 ⟨45,by decide⟩).lower ∧ (cell12556 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12556 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12556 ⟨46,by decide⟩).lower ∧ (cell12556 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12556 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12556 ⟨47,by decide⟩).lower ∧ (cell12556 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12556 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12556 ⟨48,by decide⟩).lower ∧ (cell12556 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12556 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12556 ⟨49,by decide⟩).lower ∧ (cell12556 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12556 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12556 ⟨50,by decide⟩).lower ∧ (cell12556 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12556 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12556 ⟨51,by decide⟩).lower ∧ (cell12556 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12556 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12556 ⟨52,by decide⟩).lower ∧ (cell12556 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12556 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12556 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12556 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12556,cell12556,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12556 i).lower ∧
    (cell12556 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12556 i).upper ≤ (0.532 : ℝ) ∧
    (cell12556 i).centre ≤ (0.1 : ℝ) ∧ (cell12556 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12556 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12556 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12556

/-! The local source numeric instances at 12556 have no network premises. -/
namespace BstLean.Part269.N12556
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12556)
open BstLean.Part268 (cell12556)

noncomputable def sourceNumerics12556 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12556 (cell12556 i)
      scalarRow12556.M scalarRow12556.H scalarRow12556.xi := by
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
    energy_allowance := scalarRow12556.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12556]
    centre_nonneg := (scalarRow12556.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12556])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12556
/-! Actual 12557 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12557 ≤ (1.036014341224 : ℝ) := by
  have hr : (112.058020685714 : ℝ) ≤ √(12557 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.058020685714 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12557 12557 (11 / 1000) ≤
    (0.008530286945 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12557) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.058020685714 : ℝ) ≤ √(12557 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12557)
  have hdiv : K / √(12557 : ℝ) ≤ K / 112.058020685714 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.058020685714 ≤ (0.008530286945 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12557.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12557 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12557 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12557 := gPlus_lower 12557
end BstLean.Part269.N12557

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12557
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036014341223 : ℝ) ≤ wn 12557 := by
  have hn : √(12557 : ℝ) ≤ 112.058020685715 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12557 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.058020685715 ≤ 2 / √(12557 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254799754 : ℝ) ≤ rhoBar 12557 BstLean.Part154.csC ∧
    rhoBar 12557 BstLean.Part154.csC ≤ 0.000254800148 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036014341223 : ℝ) / (1.295212 * 12557) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036014341224 : ℝ) / (1.29521 * 12557) := by gcongr
      _ ≤ (0.000254800148 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12557 BstLean.Part154.csC) ≤ 0.001019265516 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12557 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) ≤ 0.000194618177 ∧
    cc1 (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) ≤ 0.000123836817 ∧
    cc2 (rhoBar 12557 BstLean.Part154.csC) ≤ 0.000071888195 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12557 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12557 BstLean.Part154.csC * nuR (rhoBar 12557 BstLean.Part154.csC)) ≤ 0.000509616527 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254800148 : ℝ) * 0.001019265516 := by gcongr
      _ ≤ (0.000509616527 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12557 BstLean.Part154.csC) * nuR (rhoBar 12557 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019265516 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12557 BstLean.Part154.csC) * rhoBar 12557 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254800148 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254800148 / 2 + 0.399 * 0.001019265516 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194618177 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509616527 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123836817 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254800148 / 1.414213562 := by gcongr
      _ ≤ (0.000071888195 : ℝ) := by norm_num

end BstLean.Part269.N12557

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12557
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) ≤ 1.63569E-7 := by
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12557 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12557 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194618177 : ℝ) ^ 2 + 0.000123836817 ^ 2 + 3 * 0.000071888195 ^ 2 +
        2 * 0.797885 * 0.000194618177 * 0.000123836817 + 2 * 0.000194618177 * 0.000071888195 +
        4 * 0.797885 * 0.000123836817 * 0.000071888195 := by gcongr
    _ ≤ (1.63569E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12557 BstLean.Part154.csC Θ ≤ 0.002660282471 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12557 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12557 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036014341224 * 1.63569E-7 / (0.000254799754 : ℝ) := by gcongr
    _ ≤ 0.002660282471 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12557 BstLean.Part154.csC Θ ≤ 0.002952316248 + 0.000672211051 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12557 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036014341224 : ℝ) * ((2 * Θ * 0.000254800148 +
        (6863 / 10000) * 0.000254800148 * 12557 * 0.001019265516) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002952316248 + 0.000672211051 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12557 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12557 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12557 0.011 Θ ∧ gammaRatio 12557 0.011 Θ ≤ 0.000087593702 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12557 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036014341224 : ℝ) * 0.525 / ((1 - 0.011) * 12557) := by gcongr
      _ ≤ (0.000087593702 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12557 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12557 0.011 Θ) :=
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
    badAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12557 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12557 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12557 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12557 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12557 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12557 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12557 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12557 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12557 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12557 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036014341224 : ℝ) * 12557 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003696056988 + 0.003332493522 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12557

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12557
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12557 BstLean.Part154.csC) (piBar (rhoBar 12557 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12557 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12557 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12557 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12557 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12557 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12557 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12557 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12557 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12557 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052785564025 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12557) ≤ 0.010657314611 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12557 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036014341224)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010657314611 + 2 * 0.737676 / 12557) := by gcongr
    _ ≤ (0.052785564025 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12557 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12557

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12557
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497027761 : ℝ) ≤ plow 12557 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12557) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952216088)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396648298) : eMP 12557 0.011 xi bn ≤ 0.001202191437 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12557 : ℝ) * (1 - 0.011))) ≤ 0.000594398077 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396648298 / (12557 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594398077 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594398077 : ℝ) + 3.141593 * 0.052952216088 / (12557 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202191437 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952216088)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396648298) : PiBarMP 12557 12 0.011 xi bn ≤ 0.162176073502 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12557 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037371758027 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.439997307968 : ℝ) ≤ √((12557 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.058020685714 : ℝ) ≤ √(12557 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12557) ≤ 0.124332093121 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037371758027 + 0.052952216088 * 1.772454 / (2 * (111.439997307968 : ℝ))) * (1 + 0.001202191437) +
        8 / (12557 * 112.058020685714) + 0.124332093121 := by gcongr
    _ ≤ (0.162176073502 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952216088)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396648298) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282899049263) :
    parallelOracle 12557 0.011 xi bn cd ≤ 0.163178421556 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12557 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12557 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497027761 : ℝ) ≤ plow 12557 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.058020685714 : ℝ) ≤ √(12557 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282899049263 : ℝ) / (2 * 0.560497027761 * 112.058020685714)) * 0.162176073502 +
        0.282899049263 ^ 2 / (2 * 0.560497027761 * 112.058020685714) := by gcongr
    _ ≤ (0.163178421556 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052952216088) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396648298)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282899049263) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12557 12557 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497027761 : ℝ) ≤ plow 12557 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.058020685714 : ℝ) ≤ √(12557 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12557 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12557 Θ 1.22 ≤ 0.011834052502 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.058020685714 := by gcongr <;> linarith
      _ ≤ (0.011834052502 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12557 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12557 12557 0.011 ≤ 0.008530286945 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12557 12557 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12557 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12557 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12557 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12557 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163178421556 + 0.011834052502 + (0.008530286945 : ℝ) *
        (1 + 2 * (0.282899049263 + 0.011834052502) / (0.560497027761 * 112.058020685714))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12557]

end BstLean.Part269.N12557

/-! The original eight local profiles supply actual 12557 moment certificates. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12557 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052952216088 ∧
    0 ≤ bN 12557 BstLean.Part154.csC (groupTheta g) ∧ bN 12557 BstLean.Part154.csC (groupTheta g) ≤ 0.001396648298 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12557 12557 0.011
      (momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12557 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12557 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12557 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230113485238 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12557 0.011
      (momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12557 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12557
/-! The actual computed-centre upper energy formula at 12557. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12557

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12557)
open BstLean.Part268 (cell12557)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085918929860
  | 2 => 0.086869825291
  | 3 => 0.087820091811
  | 4 => 0.088771427941
  | 5 => 0.089725878313
  | 6 => 0.090685883787
  | 7 => 0.091654336042
  | 8 => 0.092634636652
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12557 12557 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12557 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12557

/-! Actual upper energy certificates on all 43 source endpoints at 12557. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12557)
open BstLean.Part268 (cell12557)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12557 (gMinus 12557) (1 - (cell12557 i).lower) ≤ 1 ∧
    energyUpper 12557 (gMinus 12557) (BstLean.Part211.gPlus 12557)
      (finiteEnergy 12557 12557 0.011) (1 - (cell12557 i).lower) ≤
      (cell12557 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨10,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨11,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨12,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨13,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨14,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨15,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨16,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨17,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨18,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨19,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨20,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨21,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨22,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨23,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨24,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨25,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨26,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨27,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨28,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨29,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨30,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨31,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨32,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨33,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨34,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨35,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨36,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨37,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨38,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨39,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨40,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨41,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨42,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨43,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨44,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨45,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨46,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨47,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨48,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨49,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨50,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨51,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12557) (by norm_num)
        (q := 1 - (cell12557 ⟨52,by decide⟩).lower)
        (by norm_num [cell12557]) (by norm_num [cell12557])
      exact ⟨E.1,E.2.trans (by norm_num [cell12557])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12557

/-! Source-cell containment and simple scalar guards at 12557. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12557)
open BstLean.Part268 (cell12557)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12557 ⟨10,by decide⟩).lower ∧ (cell12557 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12557 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12557 ⟨11,by decide⟩).lower ∧ (cell12557 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12557 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12557 ⟨12,by decide⟩).lower ∧ (cell12557 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12557 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12557 ⟨13,by decide⟩).lower ∧ (cell12557 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12557 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12557 ⟨14,by decide⟩).lower ∧ (cell12557 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12557 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12557 ⟨15,by decide⟩).lower ∧ (cell12557 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12557 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12557 ⟨16,by decide⟩).lower ∧ (cell12557 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12557 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12557 ⟨17,by decide⟩).lower ∧ (cell12557 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12557 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12557 ⟨18,by decide⟩).lower ∧ (cell12557 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12557 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12557 ⟨19,by decide⟩).lower ∧ (cell12557 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12557 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12557 ⟨20,by decide⟩).lower ∧ (cell12557 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12557 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12557 ⟨21,by decide⟩).lower ∧ (cell12557 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12557 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12557 ⟨22,by decide⟩).lower ∧ (cell12557 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12557 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12557 ⟨23,by decide⟩).lower ∧ (cell12557 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12557 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12557 ⟨24,by decide⟩).lower ∧ (cell12557 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12557 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12557 ⟨25,by decide⟩).lower ∧ (cell12557 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12557 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12557 ⟨26,by decide⟩).lower ∧ (cell12557 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12557 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12557 ⟨27,by decide⟩).lower ∧ (cell12557 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12557 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12557 ⟨28,by decide⟩).lower ∧ (cell12557 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12557 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12557 ⟨29,by decide⟩).lower ∧ (cell12557 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12557 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12557 ⟨30,by decide⟩).lower ∧ (cell12557 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12557 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12557 ⟨31,by decide⟩).lower ∧ (cell12557 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12557 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12557 ⟨32,by decide⟩).lower ∧ (cell12557 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12557 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12557 ⟨33,by decide⟩).lower ∧ (cell12557 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12557 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12557 ⟨34,by decide⟩).lower ∧ (cell12557 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12557 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12557 ⟨35,by decide⟩).lower ∧ (cell12557 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12557 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12557 ⟨36,by decide⟩).lower ∧ (cell12557 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12557 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12557 ⟨37,by decide⟩).lower ∧ (cell12557 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12557 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12557 ⟨38,by decide⟩).lower ∧ (cell12557 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12557 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12557 ⟨39,by decide⟩).lower ∧ (cell12557 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12557 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12557 ⟨40,by decide⟩).lower ∧ (cell12557 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12557 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12557 ⟨41,by decide⟩).lower ∧ (cell12557 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12557 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12557 ⟨42,by decide⟩).lower ∧ (cell12557 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12557 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12557 ⟨43,by decide⟩).lower ∧ (cell12557 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12557 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12557 ⟨44,by decide⟩).lower ∧ (cell12557 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12557 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12557 ⟨45,by decide⟩).lower ∧ (cell12557 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12557 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12557 ⟨46,by decide⟩).lower ∧ (cell12557 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12557 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12557 ⟨47,by decide⟩).lower ∧ (cell12557 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12557 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12557 ⟨48,by decide⟩).lower ∧ (cell12557 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12557 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12557 ⟨49,by decide⟩).lower ∧ (cell12557 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12557 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12557 ⟨50,by decide⟩).lower ∧ (cell12557 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12557 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12557 ⟨51,by decide⟩).lower ∧ (cell12557 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12557 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12557 ⟨52,by decide⟩).lower ∧ (cell12557 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12557 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12557 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12557 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12557,cell12557,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12557 i).lower ∧
    (cell12557 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12557 i).upper ≤ (0.532 : ℝ) ∧
    (cell12557 i).centre ≤ (0.1 : ℝ) ∧ (cell12557 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12557 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12557 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12557

/-! The local source numeric instances at 12557 have no network premises. -/
namespace BstLean.Part269.N12557
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12557)
open BstLean.Part268 (cell12557)

noncomputable def sourceNumerics12557 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12557 (cell12557 i)
      scalarRow12557.M scalarRow12557.H scalarRow12557.xi := by
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
    energy_allowance := scalarRow12557.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12557]
    centre_nonneg := (scalarRow12557.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12557])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12557
/-! Actual 12558 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12558 ≤ (1.036012894592 : ℝ) := by
  have hr : (112.062482571108 : ℝ) ≤ √(12558 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.062482571108 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12558 12558 (11 / 1000) ≤
    (0.008529947300 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12558) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.062482571108 : ℝ) ≤ √(12558 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12558)
  have hdiv : K / √(12558 : ℝ) ≤ K / 112.062482571108 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.062482571108 ≤ (0.008529947300 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12558.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12558 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12558 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12558 := gPlus_lower 12558
end BstLean.Part269.N12558

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12558
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036012894591 : ℝ) ≤ wn 12558 := by
  have hn : √(12558 : ℝ) ≤ 112.062482571109 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12558 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.062482571109 ≤ 2 / √(12558 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254779108 : ℝ) ≤ rhoBar 12558 BstLean.Part154.csC ∧
    rhoBar 12558 BstLean.Part154.csC ≤ 0.000254779503 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036012894591 : ℝ) / (1.295212 * 12558) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036012894592 : ℝ) / (1.29521 * 12558) := by gcongr
      _ ≤ (0.000254779503 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12558 BstLean.Part154.csC) ≤ 0.001019182925 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12558 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) ≤ 0.000194602407 ∧
    cc1 (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) ≤ 0.000123826782 ∧
    cc2 (rhoBar 12558 BstLean.Part154.csC) ≤ 0.000071882370 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12558 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12558 BstLean.Part154.csC * nuR (rhoBar 12558 BstLean.Part154.csC)) ≤ 0.000509575234 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254779503 : ℝ) * 0.001019182925 := by gcongr
      _ ≤ (0.000509575234 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12558 BstLean.Part154.csC) * nuR (rhoBar 12558 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019182925 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12558 BstLean.Part154.csC) * rhoBar 12558 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254779503 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254779503 / 2 + 0.399 * 0.001019182925 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194602407 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509575234 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123826782 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254779503 / 1.414213562 := by gcongr
      _ ≤ (0.000071882370 : ℝ) := by norm_num

end BstLean.Part269.N12558

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12558
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) ≤ 1.63543E-7 := by
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12558 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12558 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194602407 : ℝ) ^ 2 + 0.000123826782 ^ 2 + 3 * 0.000071882370 ^ 2 +
        2 * 0.797885 * 0.000194602407 * 0.000123826782 + 2 * 0.000194602407 * 0.000071882370 +
        4 * 0.797885 * 0.000123826782 * 0.000071882370 := by gcongr
    _ ≤ (1.63543E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12558 BstLean.Part154.csC Θ ≤ 0.002660071435 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12558 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12558 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036012894592 * 1.63543E-7 / (0.000254779108 : ℝ) := by gcongr
    _ ≤ 0.002660071435 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12558 BstLean.Part154.csC Θ ≤ 0.002952068785 + 0.000672155647 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12558 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036012894592 : ℝ) * ((2 * Θ * 0.000254779503 +
        (6863 / 10000) * 0.000254779503 * 12558 * 0.001019182925) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002952068785 + 0.000672155647 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12558 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12558 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12558 0.011 Θ ∧ gammaRatio 12558 0.011 Θ ≤ 0.000087586605 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12558 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036012894592 : ℝ) * 0.525 / ((1 - 0.011) * 12558) := by gcongr
      _ ≤ (0.000087586605 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12558 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12558 0.011 Θ) :=
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
    badAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12558 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12558 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12558 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12558 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12558 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12558 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12558 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12558 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12558 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12558 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036012894592 : ℝ) * 12558 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003695809525 + 0.003332227082 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12558

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12558
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12558 BstLean.Part154.csC) (piBar (rhoBar 12558 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12558 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12558 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12558 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12558 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12558 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12558 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12558 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12558 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12558 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052783439396 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12558) ≤ 0.010656890279 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12558 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036012894592)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010656890279 + 2 * 0.737676 / 12558) := by gcongr
    _ ≤ (0.052783439396 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12558 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12558

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12558
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497074016 : ℝ) ≤ plow 12558 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12558) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951828744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396537504) : eMP 12558 0.011 xi bn ≤ 0.001202095788 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12558 : ℝ) * (1 - 0.011))) ≤ 0.000594350835 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396537504 / (12558 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594350835 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594350835 : ℝ) + 3.141593 * 0.052951828744 / (12558 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001202095788 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951828744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396537504) : PiBarMP 12558 12 0.011 xi bn ≤ 0.162169614791 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12558 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037370275675 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.444434585133 : ℝ) ≤ √((12558 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.062482571108 : ℝ) ≤ √(12558 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12558) ≤ 0.124327142708 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037370275675 + 0.052951828744 * 1.772454 / (2 * (111.444434585133 : ℝ))) * (1 + 0.001202095788) +
        8 / (12558 * 112.062482571108) + 0.124327142708 := by gcongr
    _ ≤ (0.162169614791 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951828744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396537504) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282896082995) :
    parallelOracle 12558 0.011 xi bn cd ≤ 0.163171891119 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12558 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12558 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497074016 : ℝ) ≤ plow 12558 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.062482571108 : ℝ) ≤ √(12558 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282896082995 : ℝ) / (2 * 0.560497074016 * 112.062482571108)) * 0.162169614791 +
        0.282896082995 ^ 2 / (2 * 0.560497074016 * 112.062482571108) := by gcongr
    _ ≤ (0.163171891119 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951828744) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396537504)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282896082995) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12558 12558 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497074016 : ℝ) ≤ plow 12558 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.062482571108 : ℝ) ≤ √(12558 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12558 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12558 Θ 1.22 ≤ 0.011833581317 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.062482571108 := by gcongr <;> linarith
      _ ≤ (0.011833581317 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12558 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12558 12558 0.011 ≤ 0.008529947300 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12558 12558 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12558 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12558 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12558 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12558 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163171891119 + 0.011833581317 + (0.008529947300 : ℝ) *
        (1 + 2 * (0.282896082995 + 0.011833581317) / (0.560497074016 * 112.062482571108))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12558]

end BstLean.Part269.N12558

/-! The original eight local profiles supply actual 12558 moment certificates. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12558 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052951828744 ∧
    0 ≤ bN 12558 BstLean.Part154.csC (groupTheta g) ∧ bN 12558 BstLean.Part154.csC (groupTheta g) ≤ 0.001396537504 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12558 12558 0.011
      (momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12558 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12558 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12558 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230112643599 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12558 0.011
      (momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12558 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12558
/-! The actual computed-centre upper energy formula at 12558. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12558

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12558)
open BstLean.Part268 (cell12558)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085915847240
  | 2 => 0.086866682126
  | 3 => 0.087816878651
  | 4 => 0.088768133206
  | 5 => 0.089722487926
  | 6 => 0.090682380760
  | 7 => 0.091650700020
  | 8 => 0.092630843408
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12558 12558 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12558 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12558

/-! Actual upper energy certificates on all 43 source endpoints at 12558. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12558)
open BstLean.Part268 (cell12558)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12558 (gMinus 12558) (1 - (cell12558 i).lower) ≤ 1 ∧
    energyUpper 12558 (gMinus 12558) (BstLean.Part211.gPlus 12558)
      (finiteEnergy 12558 12558 0.011) (1 - (cell12558 i).lower) ≤
      (cell12558 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨10,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨11,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨12,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨13,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨14,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨15,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨16,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨17,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨18,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨19,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨20,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨21,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨22,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨23,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨24,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨25,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨26,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨27,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨28,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨29,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨30,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨31,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨32,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨33,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨34,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨35,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨36,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨37,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨38,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨39,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨40,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨41,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨42,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨43,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨44,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨45,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨46,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨47,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨48,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨49,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨50,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨51,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12558) (by norm_num)
        (q := 1 - (cell12558 ⟨52,by decide⟩).lower)
        (by norm_num [cell12558]) (by norm_num [cell12558])
      exact ⟨E.1,E.2.trans (by norm_num [cell12558])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12558

/-! Source-cell containment and simple scalar guards at 12558. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12558)
open BstLean.Part268 (cell12558)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12558 ⟨10,by decide⟩).lower ∧ (cell12558 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12558 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12558 ⟨11,by decide⟩).lower ∧ (cell12558 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12558 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12558 ⟨12,by decide⟩).lower ∧ (cell12558 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12558 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12558 ⟨13,by decide⟩).lower ∧ (cell12558 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12558 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12558 ⟨14,by decide⟩).lower ∧ (cell12558 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12558 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12558 ⟨15,by decide⟩).lower ∧ (cell12558 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12558 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12558 ⟨16,by decide⟩).lower ∧ (cell12558 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12558 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12558 ⟨17,by decide⟩).lower ∧ (cell12558 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12558 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12558 ⟨18,by decide⟩).lower ∧ (cell12558 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12558 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12558 ⟨19,by decide⟩).lower ∧ (cell12558 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12558 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12558 ⟨20,by decide⟩).lower ∧ (cell12558 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12558 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12558 ⟨21,by decide⟩).lower ∧ (cell12558 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12558 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12558 ⟨22,by decide⟩).lower ∧ (cell12558 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12558 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12558 ⟨23,by decide⟩).lower ∧ (cell12558 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12558 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12558 ⟨24,by decide⟩).lower ∧ (cell12558 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12558 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12558 ⟨25,by decide⟩).lower ∧ (cell12558 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12558 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12558 ⟨26,by decide⟩).lower ∧ (cell12558 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12558 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12558 ⟨27,by decide⟩).lower ∧ (cell12558 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12558 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12558 ⟨28,by decide⟩).lower ∧ (cell12558 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12558 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12558 ⟨29,by decide⟩).lower ∧ (cell12558 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12558 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12558 ⟨30,by decide⟩).lower ∧ (cell12558 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12558 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12558 ⟨31,by decide⟩).lower ∧ (cell12558 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12558 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12558 ⟨32,by decide⟩).lower ∧ (cell12558 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12558 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12558 ⟨33,by decide⟩).lower ∧ (cell12558 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12558 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12558 ⟨34,by decide⟩).lower ∧ (cell12558 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12558 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12558 ⟨35,by decide⟩).lower ∧ (cell12558 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12558 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12558 ⟨36,by decide⟩).lower ∧ (cell12558 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12558 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12558 ⟨37,by decide⟩).lower ∧ (cell12558 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12558 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12558 ⟨38,by decide⟩).lower ∧ (cell12558 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12558 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12558 ⟨39,by decide⟩).lower ∧ (cell12558 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12558 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12558 ⟨40,by decide⟩).lower ∧ (cell12558 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12558 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12558 ⟨41,by decide⟩).lower ∧ (cell12558 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12558 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12558 ⟨42,by decide⟩).lower ∧ (cell12558 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12558 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12558 ⟨43,by decide⟩).lower ∧ (cell12558 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12558 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12558 ⟨44,by decide⟩).lower ∧ (cell12558 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12558 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12558 ⟨45,by decide⟩).lower ∧ (cell12558 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12558 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12558 ⟨46,by decide⟩).lower ∧ (cell12558 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12558 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12558 ⟨47,by decide⟩).lower ∧ (cell12558 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12558 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12558 ⟨48,by decide⟩).lower ∧ (cell12558 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12558 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12558 ⟨49,by decide⟩).lower ∧ (cell12558 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12558 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12558 ⟨50,by decide⟩).lower ∧ (cell12558 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12558 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12558 ⟨51,by decide⟩).lower ∧ (cell12558 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12558 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12558 ⟨52,by decide⟩).lower ∧ (cell12558 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12558 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12558 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12558 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12558,cell12558,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12558 i).lower ∧
    (cell12558 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12558 i).upper ≤ (0.532 : ℝ) ∧
    (cell12558 i).centre ≤ (0.1 : ℝ) ∧ (cell12558 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12558 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12558 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12558

/-! The local source numeric instances at 12558 have no network premises. -/
namespace BstLean.Part269.N12558
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12558)
open BstLean.Part268 (cell12558)

noncomputable def sourceNumerics12558 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12558 (cell12558 i)
      scalarRow12558.M scalarRow12558.H scalarRow12558.xi := by
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
    energy_allowance := scalarRow12558.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12558]
    centre_nonneg := (scalarRow12558.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12558])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12558
/-! Actual 12559 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12559 ≤ (1.036011448135 : ℝ) := by
  have hr : (112.066944278855 : ℝ) ≤ √(12559 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.066944278855 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12559 12559 (11 / 1000) ≤
    (0.008529607696 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12559) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.066944278855 : ℝ) ≤ √(12559 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12559)
  have hdiv : K / √(12559 : ℝ) ≤ K / 112.066944278855 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.066944278855 ≤ (0.008529607696 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12559.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12559 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12559 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12559 := gPlus_lower 12559
end BstLean.Part269.N12559

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12559
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036011448134 : ℝ) ≤ wn 12559 := by
  have hn : √(12559 : ℝ) ≤ 112.066944278856 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12559 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.066944278856 ≤ 2 / √(12559 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254758466 : ℝ) ≤ rhoBar 12559 BstLean.Part154.csC ∧
    rhoBar 12559 BstLean.Part154.csC ≤ 0.000254758860 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036011448134 : ℝ) / (1.295212 * 12559) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036011448135 : ℝ) / (1.29521 * 12559) := by gcongr
      _ ≤ (0.000254758860 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12559 BstLean.Part154.csC) ≤ 0.001019100343 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12559 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) ≤ 0.000194586639 ∧
    cc1 (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) ≤ 0.000123816749 ∧
    cc2 (rhoBar 12559 BstLean.Part154.csC) ≤ 0.000071876546 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12559 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12559 BstLean.Part154.csC * nuR (rhoBar 12559 BstLean.Part154.csC)) ≤ 0.000509533946 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254758860 : ℝ) * 0.001019100343 := by gcongr
      _ ≤ (0.000509533946 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12559 BstLean.Part154.csC) * nuR (rhoBar 12559 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019100343 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12559 BstLean.Part154.csC) * rhoBar 12559 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254758860 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254758860 / 2 + 0.399 * 0.001019100343 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194586639 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509533946 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123816749 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254758860 / 1.414213562 := by gcongr
      _ ≤ (0.000071876546 : ℝ) := by norm_num

end BstLean.Part269.N12559

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12559
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) ≤ 1.63516E-7 := by
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12559 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12559 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194586639 : ℝ) ^ 2 + 0.000123816749 ^ 2 + 3 * 0.000071876546 ^ 2 +
        2 * 0.797885 * 0.000194586639 * 0.000123816749 + 2 * 0.000194586639 * 0.000071876546 +
        4 * 0.797885 * 0.000123816749 * 0.000071876546 := by gcongr
    _ ≤ (1.63516E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12559 BstLean.Part154.csC Θ ≤ 0.002659844058 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12559 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12559 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036011448135 * 1.63516E-7 / (0.000254758466 : ℝ) := by gcongr
    _ ≤ 0.002659844058 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12559 BstLean.Part154.csC Θ ≤ 0.002951821335 + 0.000672100249 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12559 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036011448135 : ℝ) * ((2 * Θ * 0.000254758860 +
        (6863 / 10000) * 0.000254758860 * 12559 * 0.001019100343) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002951821335 + 0.000672100249 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12559 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12559 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12559 0.011 Θ ∧ gammaRatio 12559 0.011 Θ ≤ 0.000087579509 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12559 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036011448135 : ℝ) * 0.525 / ((1 - 0.011) * 12559) := by gcongr
      _ ≤ (0.000087579509 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12559 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12559 0.011 Θ) :=
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
    badAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12559 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12559 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12559 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12559 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12559 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12559 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12559 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12559 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12559 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12559 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036011448135 : ℝ) * 12559 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003695562075 + 0.003331944307 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12559

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12559
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12559 BstLean.Part154.csC) (piBar (rhoBar 12559 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12559 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12559 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12559 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12559 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12559 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12559 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12559 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12559 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12559 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052781315020 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12559) ≤ 0.010656465997 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12559 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036011448135)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010656465997 + 2 * 0.737676 / 12559) := by gcongr
    _ ≤ (0.052781315020 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12559 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12559

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12559
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497120264 : ℝ) ≤ plow 12559 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12559) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951432837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396418131) : eMP 12559 0.011 xi bn ≤ 0.001201996494 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12559 : ℝ) * (1 - 0.011))) ≤ 0.000594301771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396418131 / (12559 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594301771 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594301771 : ℝ) + 3.141593 * 0.052951432837 / (12559 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201996494 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951432837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396418131) : PiBarMP 12559 12 0.011 xi bn ≤ 0.162163041482 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12559 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037368678476 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.448871685629 : ℝ) ≤ √((12559 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.066944278855 : ℝ) ≤ √(12559 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12559) ≤ 0.124322192886 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037368678476 + 0.052951432837 * 1.772454 / (2 * (111.448871685629 : ℝ))) * (1 + 0.001201996494) +
        8 / (12559 * 112.066944278855) + 0.124322192886 := by gcongr
    _ ≤ (0.162163041482 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951432837)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396418131) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282893098372) :
    parallelOracle 12559 0.011 xi bn cd ≤ 0.163165245727 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12559 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12559 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497120264 : ℝ) ≤ plow 12559 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.066944278855 : ℝ) ≤ √(12559 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282893098372 : ℝ) / (2 * 0.560497120264 * 112.066944278855)) * 0.162163041482 +
        0.282893098372 ^ 2 / (2 * 0.560497120264 * 112.066944278855) := by gcongr
    _ ≤ (0.163165245727 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951432837) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396418131)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282893098372) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12559 12559 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497120264 : ℝ) ≤ plow 12559 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.066944278855 : ℝ) ≤ √(12559 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12559 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12559 Θ 1.22 ≤ 0.011833110188 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.066944278855 := by gcongr <;> linarith
      _ ≤ (0.011833110188 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12559 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12559 12559 0.011 ≤ 0.008529607696 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12559 12559 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12559 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12559 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12559 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12559 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163165245727 + 0.011833110188 + (0.008529607696 : ℝ) *
        (1 + 2 * (0.282893098372 + 0.011833110188) / (0.560497120264 * 112.066944278855))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12559]

end BstLean.Part269.N12559

/-! The original eight local profiles supply actual 12559 moment certificates. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12559 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052951432837 ∧
    0 ≤ bN 12559 BstLean.Part154.csC (groupTheta g) ∧ bN 12559 BstLean.Part154.csC (groupTheta g) ≤ 0.001396418131 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12559 12559 0.011
      (momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12559 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12559 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12559 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230111783352 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12559 0.011
      (momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12559 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12559
/-! The actual computed-centre upper energy formula at 12559. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12559

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12559)
open BstLean.Part268 (cell12559)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085912765874
  | 2 => 0.086863540270
  | 3 => 0.087813666866
  | 4 => 0.088764839927
  | 5 => 0.089719099093
  | 6 => 0.090678879407
  | 7 => 0.091647065819
  | 8 => 0.092627052158
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12559 12559 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12559 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12559

/-! Actual upper energy certificates on all 43 source endpoints at 12559. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12559)
open BstLean.Part268 (cell12559)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12559 (gMinus 12559) (1 - (cell12559 i).lower) ≤ 1 ∧
    energyUpper 12559 (gMinus 12559) (BstLean.Part211.gPlus 12559)
      (finiteEnergy 12559 12559 0.011) (1 - (cell12559 i).lower) ≤
      (cell12559 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨10,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨11,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨12,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨13,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨14,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨15,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨16,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨17,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨18,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨19,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨20,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨21,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨22,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨23,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨24,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨25,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨26,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨27,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨28,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨29,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨30,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨31,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨32,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨33,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨34,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨35,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨36,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨37,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨38,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨39,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨40,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨41,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨42,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨43,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨44,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨45,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨46,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨47,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨48,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨49,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨50,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨51,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12559) (by norm_num)
        (q := 1 - (cell12559 ⟨52,by decide⟩).lower)
        (by norm_num [cell12559]) (by norm_num [cell12559])
      exact ⟨E.1,E.2.trans (by norm_num [cell12559])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12559

/-! Source-cell containment and simple scalar guards at 12559. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12559)
open BstLean.Part268 (cell12559)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12559 ⟨10,by decide⟩).lower ∧ (cell12559 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12559 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12559 ⟨11,by decide⟩).lower ∧ (cell12559 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12559 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12559 ⟨12,by decide⟩).lower ∧ (cell12559 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12559 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12559 ⟨13,by decide⟩).lower ∧ (cell12559 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12559 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12559 ⟨14,by decide⟩).lower ∧ (cell12559 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12559 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12559 ⟨15,by decide⟩).lower ∧ (cell12559 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12559 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12559 ⟨16,by decide⟩).lower ∧ (cell12559 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12559 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12559 ⟨17,by decide⟩).lower ∧ (cell12559 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12559 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12559 ⟨18,by decide⟩).lower ∧ (cell12559 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12559 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12559 ⟨19,by decide⟩).lower ∧ (cell12559 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12559 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12559 ⟨20,by decide⟩).lower ∧ (cell12559 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12559 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12559 ⟨21,by decide⟩).lower ∧ (cell12559 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12559 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12559 ⟨22,by decide⟩).lower ∧ (cell12559 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12559 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12559 ⟨23,by decide⟩).lower ∧ (cell12559 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12559 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12559 ⟨24,by decide⟩).lower ∧ (cell12559 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12559 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12559 ⟨25,by decide⟩).lower ∧ (cell12559 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12559 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12559 ⟨26,by decide⟩).lower ∧ (cell12559 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12559 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12559 ⟨27,by decide⟩).lower ∧ (cell12559 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12559 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12559 ⟨28,by decide⟩).lower ∧ (cell12559 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12559 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12559 ⟨29,by decide⟩).lower ∧ (cell12559 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12559 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12559 ⟨30,by decide⟩).lower ∧ (cell12559 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12559 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12559 ⟨31,by decide⟩).lower ∧ (cell12559 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12559 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12559 ⟨32,by decide⟩).lower ∧ (cell12559 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12559 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12559 ⟨33,by decide⟩).lower ∧ (cell12559 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12559 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12559 ⟨34,by decide⟩).lower ∧ (cell12559 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12559 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12559 ⟨35,by decide⟩).lower ∧ (cell12559 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12559 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12559 ⟨36,by decide⟩).lower ∧ (cell12559 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12559 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12559 ⟨37,by decide⟩).lower ∧ (cell12559 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12559 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12559 ⟨38,by decide⟩).lower ∧ (cell12559 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12559 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12559 ⟨39,by decide⟩).lower ∧ (cell12559 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12559 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12559 ⟨40,by decide⟩).lower ∧ (cell12559 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12559 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12559 ⟨41,by decide⟩).lower ∧ (cell12559 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12559 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12559 ⟨42,by decide⟩).lower ∧ (cell12559 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12559 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12559 ⟨43,by decide⟩).lower ∧ (cell12559 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12559 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12559 ⟨44,by decide⟩).lower ∧ (cell12559 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12559 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12559 ⟨45,by decide⟩).lower ∧ (cell12559 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12559 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12559 ⟨46,by decide⟩).lower ∧ (cell12559 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12559 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12559 ⟨47,by decide⟩).lower ∧ (cell12559 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12559 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12559 ⟨48,by decide⟩).lower ∧ (cell12559 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12559 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12559 ⟨49,by decide⟩).lower ∧ (cell12559 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12559 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12559 ⟨50,by decide⟩).lower ∧ (cell12559 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12559 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12559 ⟨51,by decide⟩).lower ∧ (cell12559 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12559 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12559 ⟨52,by decide⟩).lower ∧ (cell12559 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12559 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12559 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12559 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12559,cell12559,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12559 i).lower ∧
    (cell12559 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12559 i).upper ≤ (0.532 : ℝ) ∧
    (cell12559 i).centre ≤ (0.1 : ℝ) ∧ (cell12559 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12559 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12559 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12559

/-! The local source numeric instances at 12559 have no network premises. -/
namespace BstLean.Part269.N12559
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12559)
open BstLean.Part268 (cell12559)

noncomputable def sourceNumerics12559 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12559 (cell12559 i)
      scalarRow12559.M scalarRow12559.H scalarRow12559.xi := by
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
    energy_allowance := scalarRow12559.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12559]
    centre_nonneg := (scalarRow12559.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12559])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12559
/-! Actual 12560 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12560 ≤ (1.036010001850 : ℝ) := by
  have hr : (112.071405808975 : ℝ) ≤ √(12560 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.071405808975 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12560 12560 (11 / 1000) ≤
    (0.008529268132 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12560) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.071405808975 : ℝ) ≤ √(12560 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12560)
  have hdiv : K / √(12560 : ℝ) ≤ K / 112.071405808975 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.071405808975 ≤ (0.008529268132 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12560.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12560 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12560 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12560 := gPlus_lower 12560
end BstLean.Part269.N12560

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12560
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036010001849 : ℝ) ≤ wn 12560 := by
  have hn : √(12560 : ℝ) ≤ 112.071405808976 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12560 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.071405808976 ≤ 2 / √(12560 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254737827 : ℝ) ≤ rhoBar 12560 BstLean.Part154.csC ∧
    rhoBar 12560 BstLean.Part154.csC ≤ 0.000254738221 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036010001849 : ℝ) / (1.295212 * 12560) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036010001850 : ℝ) / (1.29521 * 12560) := by gcongr
      _ ≤ (0.000254738221 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12560 BstLean.Part154.csC) ≤ 0.001019017776 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12560 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) ≤ 0.000194570874 ∧
    cc1 (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) ≤ 0.000123806718 ∧
    cc2 (rhoBar 12560 BstLean.Part154.csC) ≤ 0.000071870723 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12560 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12560 BstLean.Part154.csC * nuR (rhoBar 12560 BstLean.Part154.csC)) ≤ 0.000509492665 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254738221 : ℝ) * 0.001019017776 := by gcongr
      _ ≤ (0.000509492665 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12560 BstLean.Part154.csC) * nuR (rhoBar 12560 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001019017776 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12560 BstLean.Part154.csC) * rhoBar 12560 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254738221 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254738221 / 2 + 0.399 * 0.001019017776 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194570874 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509492665 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123806718 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254738221 / 1.414213562 := by gcongr
      _ ≤ (0.000071870723 : ℝ) := by norm_num

end BstLean.Part269.N12560

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12560
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) ≤ 1.63490E-7 := by
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12560 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12560 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194570874 : ℝ) ^ 2 + 0.000123806718 ^ 2 + 3 * 0.000071870723 ^ 2 +
        2 * 0.797885 * 0.000194570874 * 0.000123806718 + 2 * 0.000194570874 * 0.000071870723 +
        4 * 0.797885 * 0.000123806718 * 0.000071870723 := by gcongr
    _ ≤ (1.63490E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12560 BstLean.Part154.csC Θ ≤ 0.002659632882 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12560 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12560 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036010001850 * 1.63490E-7 / (0.000254737827 : ℝ) := by gcongr
    _ ≤ 0.002659632882 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12560 BstLean.Part154.csC Θ ≤ 0.002951573939 + 0.000672044861 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12560 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036010001850 : ℝ) * ((2 * Θ * 0.000254738221 +
        (6863 / 10000) * 0.000254738221 * 12560 * 0.001019017776) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002951573939 + 0.000672044861 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12560 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12560 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12560 0.011 Θ ∧ gammaRatio 12560 0.011 Θ ≤ 0.000087572413 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12560 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036010001850 : ℝ) * 0.525 / ((1 - 0.011) * 12560) := by gcongr
      _ ≤ (0.000087572413 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12560 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12560 0.011 Θ) :=
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
    badAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12560 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12560 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12560 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12560 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12560 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12560 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12560 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12560 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12560 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12560 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036010001850 : ℝ) * 12560 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003695314679 + 0.003331677743 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12560

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12560
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12560 BstLean.Part154.csC) (piBar (rhoBar 12560 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12560 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12560 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12560 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12560 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12560 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12560 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12560 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12560 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12560 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052779190901 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12560) ≤ 0.010656041766 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12560 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036010001850)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010656041766 + 2 * 0.737676 / 12560) := by gcongr
    _ ≤ (0.052779190901 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12560 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12560

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12560
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497166504 : ℝ) ≤ plow 12560 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12560) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951045495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396307264) : eMP 12560 0.011 xi bn ≤ 0.001201900827 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12560 : ℝ) * (1 - 0.011))) ≤ 0.000594254520 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396307264 / (12560 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594254520 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594254520 : ℝ) + 3.141593 * 0.052951045495 / (12560 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201900827 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951045495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396307264) : PiBarMP 12560 12 0.011 xi bn ≤ 0.162156582858 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12560 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037367195025 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.453308609480 : ℝ) ≤ √((12560 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.071405808975 : ℝ) ≤ √(12560 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12560) ≤ 0.124317243656 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037367195025 + 0.052951045495 * 1.772454 / (2 * (111.453308609480 : ℝ))) * (1 + 0.001201900827) +
        8 / (12560 * 112.071405808975) + 0.124317243656 := by gcongr
    _ ≤ (0.162156582858 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951045495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396307264) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282890132612) :
    parallelOracle 12560 0.011 xi bn cd ≤ 0.163158715395 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12560 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12560 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497166504 : ℝ) ≤ plow 12560 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.071405808975 : ℝ) ≤ √(12560 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282890132612 : ℝ) / (2 * 0.560497166504 * 112.071405808975)) * 0.162156582858 +
        0.282890132612 ^ 2 / (2 * 0.560497166504 * 112.071405808975) := by gcongr
    _ ≤ (0.163158715395 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052951045495) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396307264)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282890132612) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12560 12560 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497166504 : ℝ) ≤ plow 12560 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.071405808975 : ℝ) ≤ √(12560 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12560 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12560 Θ 1.22 ≤ 0.011832639115 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.071405808975 := by gcongr <;> linarith
      _ ≤ (0.011832639115 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12560 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12560 12560 0.011 ≤ 0.008529268132 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12560 12560 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12560 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12560 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12560 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12560 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163158715395 + 0.011832639115 + (0.008529268132 : ℝ) *
        (1 + 2 * (0.282890132612 + 0.011832639115) / (0.560497166504 * 112.071405808975))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12560]

end BstLean.Part269.N12560

/-! The original eight local profiles supply actual 12560 moment certificates. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12560 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052951045495 ∧
    0 ≤ bN 12560 BstLean.Part154.csC (groupTheta g) ∧ bN 12560 BstLean.Part154.csC (groupTheta g) ≤ 0.001396307264 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12560 12560 0.011
      (momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12560 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12560 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12560 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230110941711 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12560 0.011
      (momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12560 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12560
/-! The actual computed-centre upper energy formula at 12560. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12560

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12560)
open BstLean.Part268 (cell12560)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085909685762
  | 2 => 0.086860399721
  | 3 => 0.087810456455
  | 4 => 0.088761548102
  | 5 => 0.089715711813
  | 6 => 0.090675379728
  | 7 => 0.091643433435
  | 8 => 0.092623262900
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12560 12560 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12560 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12560

/-! Actual upper energy certificates on all 43 source endpoints at 12560. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12560)
open BstLean.Part268 (cell12560)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12560 (gMinus 12560) (1 - (cell12560 i).lower) ≤ 1 ∧
    energyUpper 12560 (gMinus 12560) (BstLean.Part211.gPlus 12560)
      (finiteEnergy 12560 12560 0.011) (1 - (cell12560 i).lower) ≤
      (cell12560 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨10,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨11,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨12,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨13,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨14,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨15,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨16,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨17,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨18,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨19,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨20,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨21,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨22,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨23,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨24,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨25,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨26,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨27,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨28,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨29,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨30,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨31,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨32,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨33,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨34,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨35,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨36,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨37,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨38,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨39,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨40,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨41,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨42,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨43,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨44,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨45,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨46,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨47,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨48,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨49,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨50,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨51,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12560) (by norm_num)
        (q := 1 - (cell12560 ⟨52,by decide⟩).lower)
        (by norm_num [cell12560]) (by norm_num [cell12560])
      exact ⟨E.1,E.2.trans (by norm_num [cell12560])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12560

/-! Source-cell containment and simple scalar guards at 12560. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12560)
open BstLean.Part268 (cell12560)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12560 ⟨10,by decide⟩).lower ∧ (cell12560 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12560 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12560 ⟨11,by decide⟩).lower ∧ (cell12560 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12560 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12560 ⟨12,by decide⟩).lower ∧ (cell12560 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12560 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12560 ⟨13,by decide⟩).lower ∧ (cell12560 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12560 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12560 ⟨14,by decide⟩).lower ∧ (cell12560 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12560 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12560 ⟨15,by decide⟩).lower ∧ (cell12560 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12560 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12560 ⟨16,by decide⟩).lower ∧ (cell12560 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12560 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12560 ⟨17,by decide⟩).lower ∧ (cell12560 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12560 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12560 ⟨18,by decide⟩).lower ∧ (cell12560 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12560 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12560 ⟨19,by decide⟩).lower ∧ (cell12560 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12560 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12560 ⟨20,by decide⟩).lower ∧ (cell12560 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12560 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12560 ⟨21,by decide⟩).lower ∧ (cell12560 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12560 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12560 ⟨22,by decide⟩).lower ∧ (cell12560 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12560 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12560 ⟨23,by decide⟩).lower ∧ (cell12560 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12560 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12560 ⟨24,by decide⟩).lower ∧ (cell12560 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12560 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12560 ⟨25,by decide⟩).lower ∧ (cell12560 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12560 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12560 ⟨26,by decide⟩).lower ∧ (cell12560 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12560 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12560 ⟨27,by decide⟩).lower ∧ (cell12560 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12560 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12560 ⟨28,by decide⟩).lower ∧ (cell12560 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12560 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12560 ⟨29,by decide⟩).lower ∧ (cell12560 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12560 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12560 ⟨30,by decide⟩).lower ∧ (cell12560 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12560 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12560 ⟨31,by decide⟩).lower ∧ (cell12560 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12560 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12560 ⟨32,by decide⟩).lower ∧ (cell12560 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12560 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12560 ⟨33,by decide⟩).lower ∧ (cell12560 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12560 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12560 ⟨34,by decide⟩).lower ∧ (cell12560 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12560 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12560 ⟨35,by decide⟩).lower ∧ (cell12560 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12560 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12560 ⟨36,by decide⟩).lower ∧ (cell12560 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12560 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12560 ⟨37,by decide⟩).lower ∧ (cell12560 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12560 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12560 ⟨38,by decide⟩).lower ∧ (cell12560 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12560 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12560 ⟨39,by decide⟩).lower ∧ (cell12560 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12560 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12560 ⟨40,by decide⟩).lower ∧ (cell12560 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12560 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12560 ⟨41,by decide⟩).lower ∧ (cell12560 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12560 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12560 ⟨42,by decide⟩).lower ∧ (cell12560 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12560 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12560 ⟨43,by decide⟩).lower ∧ (cell12560 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12560 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12560 ⟨44,by decide⟩).lower ∧ (cell12560 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12560 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12560 ⟨45,by decide⟩).lower ∧ (cell12560 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12560 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12560 ⟨46,by decide⟩).lower ∧ (cell12560 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12560 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12560 ⟨47,by decide⟩).lower ∧ (cell12560 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12560 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12560 ⟨48,by decide⟩).lower ∧ (cell12560 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12560 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12560 ⟨49,by decide⟩).lower ∧ (cell12560 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12560 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12560 ⟨50,by decide⟩).lower ∧ (cell12560 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12560 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12560 ⟨51,by decide⟩).lower ∧ (cell12560 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12560 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12560 ⟨52,by decide⟩).lower ∧ (cell12560 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12560 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12560 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12560 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12560,cell12560,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12560 i).lower ∧
    (cell12560 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12560 i).upper ≤ (0.532 : ℝ) ∧
    (cell12560 i).centre ≤ (0.1 : ℝ) ∧ (cell12560 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12560 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12560 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12560

/-! The local source numeric instances at 12560 have no network premises. -/
namespace BstLean.Part269.N12560
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12560)
open BstLean.Part268 (cell12560)

noncomputable def sourceNumerics12560 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12560 (cell12560 i)
      scalarRow12560.M scalarRow12560.H scalarRow12560.xi := by
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
    energy_allowance := scalarRow12560.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12560]
    centre_nonneg := (scalarRow12560.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12560])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12560
/-! Actual 12561 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12561 ≤ (1.036008555740 : ℝ) := by
  have hr : (112.075867161490 : ℝ) ≤ √(12561 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.075867161490 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12561 12561 (11 / 1000) ≤
    (0.008528928609 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12561) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.075867161490 : ℝ) ≤ √(12561 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12561)
  have hdiv : K / √(12561 : ℝ) ≤ K / 112.075867161490 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.075867161490 ≤ (0.008528928609 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12561.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12561 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12561 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12561 := gPlus_lower 12561
end BstLean.Part269.N12561

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12561
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036008555739 : ℝ) ≤ wn 12561 := by
  have hn : √(12561 : ℝ) ≤ 112.075867161491 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12561 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.075867161491 ≤ 2 / √(12561 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254717191 : ℝ) ≤ rhoBar 12561 BstLean.Part154.csC ∧
    rhoBar 12561 BstLean.Part154.csC ≤ 0.000254717586 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036008555739 : ℝ) / (1.295212 * 12561) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036008555740 : ℝ) / (1.29521 * 12561) := by gcongr
      _ ≤ (0.000254717586 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12561 BstLean.Part154.csC) ≤ 0.001018935226 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12561 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) ≤ 0.000194555113 ∧
    cc1 (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) ≤ 0.000123796689 ∧
    cc2 (rhoBar 12561 BstLean.Part154.csC) ≤ 0.000071864901 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12561 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12561 BstLean.Part154.csC * nuR (rhoBar 12561 BstLean.Part154.csC)) ≤ 0.000509451393 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254717586 : ℝ) * 0.001018935226 := by gcongr
      _ ≤ (0.000509451393 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12561 BstLean.Part154.csC) * nuR (rhoBar 12561 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018935226 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12561 BstLean.Part154.csC) * rhoBar 12561 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254717586 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254717586 / 2 + 0.399 * 0.001018935226 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194555113 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509451393 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123796689 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254717586 / 1.414213562 := by gcongr
      _ ≤ (0.000071864901 : ℝ) := by norm_num

end BstLean.Part269.N12561

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12561
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) ≤ 1.63463E-7 := by
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12561 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12561 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194555113 : ℝ) ^ 2 + 0.000123796689 ^ 2 + 3 * 0.000071864901 ^ 2 +
        2 * 0.797885 * 0.000194555113 * 0.000123796689 + 2 * 0.000194555113 * 0.000071864901 +
        4 * 0.797885 * 0.000123796689 * 0.000071864901 := by gcongr
    _ ≤ (1.63463E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12561 BstLean.Part154.csC Θ ≤ 0.002659405373 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12561 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12561 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036008555740 * 1.63463E-7 / (0.000254717191 : ℝ) := by gcongr
    _ ≤ 0.002659405373 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12561 BstLean.Part154.csC Θ ≤ 0.002951326602 + 0.000671989485 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12561 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036008555740 : ℝ) * ((2 * Θ * 0.000254717586 +
        (6863 / 10000) * 0.000254717586 * 12561 * 0.001018935226) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002951326602 + 0.000671989485 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12561 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12561 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12561 0.011 Θ ∧ gammaRatio 12561 0.011 Θ ≤ 0.000087565319 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12561 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036008555740 : ℝ) * 0.525 / ((1 - 0.011) * 12561) := by gcongr
      _ ≤ (0.000087565319 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12561 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12561 0.011 Θ) :=
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
    badAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12561 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12561 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12561 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12561 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12561 0.011 Θ) 1.12 ≤ 3.3895E-8 := by
    have he : (17.2 : ℝ) ≤ gap 1 (gammaRatio 12561 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12561 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12561 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12561 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12561 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036008555740 : ℝ) * 12561 *
        (2.7751E-8 / 1.1045361 + 3.3895E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003695067342 + 0.003331394858 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12561

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12561
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12561 BstLean.Part154.csC) (piBar (rhoBar 12561 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12561 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12561 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12561 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12561 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12561 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12561 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12561 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12561 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12561 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052777067038 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12561) ≤ 0.010655617586 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12561 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036008555740)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010655617586 + 2 * 0.737676 / 12561) := by gcongr
    _ ≤ (0.052777067038 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12561 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12561

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12561
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497212737 : ℝ) ≤ plow 12561 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12561) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950649643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396187821) : eMP 12561 0.011 xi bn ≤ 0.001201801519 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12561 : ℝ) * (1 - 0.011))) ≤ 0.000594205449 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396187821 / (12561 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594205449 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594205449 : ℝ) + 3.141593 * 0.052950649643 / (12561 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201801519 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950649643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396187821) : PiBarMP 12561 12 0.011 xi bn ≤ 0.162150009666 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12561 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037365596757 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.457745356704 : ℝ) ≤ √((12561 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.075867161490 : ℝ) ≤ √(12561 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12561) ≤ 0.124312295016 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037365596757 + 0.052950649643 * 1.772454 / (2 * (111.457745356704 : ℝ))) * (1 + 0.001201801519) +
        8 / (12561 * 112.075867161490) + 0.124312295016 := by gcongr
    _ ≤ (0.162150009666 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950649643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396187821) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282887148615) :
    parallelOracle 12561 0.011 xi bn cd ≤ 0.163152070139 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12561 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12561 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497212737 : ℝ) ≤ plow 12561 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.075867161490 : ℝ) ≤ √(12561 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282887148615 : ℝ) / (2 * 0.560497212737 * 112.075867161490)) * 0.162150009666 +
        0.282887148615 ^ 2 / (2 * 0.560497212737 * 112.075867161490) := by gcongr
    _ ≤ (0.163152070139 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950649643) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396187821)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282887148615) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12561 12561 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497212737 : ℝ) ≤ plow 12561 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.075867161490 : ℝ) ≤ √(12561 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12561 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12561 Θ 1.22 ≤ 0.011832168099 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.075867161490 := by gcongr <;> linarith
      _ ≤ (0.011832168099 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12561 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12561 12561 0.011 ≤ 0.008528928609 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12561 12561 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12561 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12561 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12561 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12561 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163152070139 + 0.011832168099 + (0.008528928609 : ℝ) *
        (1 + 2 * (0.282887148615 + 0.011832168099) / (0.560497212737 * 112.075867161490))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12561]

end BstLean.Part269.N12561

/-! The original eight local profiles supply actual 12561 moment certificates. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12561 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052950649643 ∧
    0 ≤ bN 12561 BstLean.Part154.csC (groupTheta g) ∧ bN 12561 BstLean.Part154.csC (groupTheta g) ≤ 0.001396187821 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12561 12561 0.011
      (momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12561 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12561 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12561 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230110081577 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12561 0.011
      (momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12561 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12561
/-! The actual computed-centre upper energy formula at 12561. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12561

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12561)
open BstLean.Part268 (cell12561)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085906606902
  | 2 => 0.086857260478
  | 3 => 0.087807247415
  | 4 => 0.088758257730
  | 5 => 0.089712326085
  | 6 => 0.090671881720
  | 7 => 0.091639802868
  | 8 => 0.092619475633
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12561 12561 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12561 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12561

/-! Actual upper energy certificates on all 43 source endpoints at 12561. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12561)
open BstLean.Part268 (cell12561)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12561 (gMinus 12561) (1 - (cell12561 i).lower) ≤ 1 ∧
    energyUpper 12561 (gMinus 12561) (BstLean.Part211.gPlus 12561)
      (finiteEnergy 12561 12561 0.011) (1 - (cell12561 i).lower) ≤
      (cell12561 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨10,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨11,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨12,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨13,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨14,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨15,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨16,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨17,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨18,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨19,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨20,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨21,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨22,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨23,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨24,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨25,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨26,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨27,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨28,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨29,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨30,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨31,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨32,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨33,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨34,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨35,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨36,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨37,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨38,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨39,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨40,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨41,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨42,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨43,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨44,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨45,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨46,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨47,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨48,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨49,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨50,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨51,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12561) (by norm_num)
        (q := 1 - (cell12561 ⟨52,by decide⟩).lower)
        (by norm_num [cell12561]) (by norm_num [cell12561])
      exact ⟨E.1,E.2.trans (by norm_num [cell12561])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12561

/-! Source-cell containment and simple scalar guards at 12561. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12561)
open BstLean.Part268 (cell12561)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12561 ⟨10,by decide⟩).lower ∧ (cell12561 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12561 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12561 ⟨11,by decide⟩).lower ∧ (cell12561 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12561 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12561 ⟨12,by decide⟩).lower ∧ (cell12561 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12561 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12561 ⟨13,by decide⟩).lower ∧ (cell12561 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12561 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12561 ⟨14,by decide⟩).lower ∧ (cell12561 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12561 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12561 ⟨15,by decide⟩).lower ∧ (cell12561 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12561 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12561 ⟨16,by decide⟩).lower ∧ (cell12561 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12561 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12561 ⟨17,by decide⟩).lower ∧ (cell12561 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12561 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12561 ⟨18,by decide⟩).lower ∧ (cell12561 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12561 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12561 ⟨19,by decide⟩).lower ∧ (cell12561 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12561 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12561 ⟨20,by decide⟩).lower ∧ (cell12561 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12561 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12561 ⟨21,by decide⟩).lower ∧ (cell12561 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12561 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12561 ⟨22,by decide⟩).lower ∧ (cell12561 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12561 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12561 ⟨23,by decide⟩).lower ∧ (cell12561 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12561 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12561 ⟨24,by decide⟩).lower ∧ (cell12561 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12561 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12561 ⟨25,by decide⟩).lower ∧ (cell12561 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12561 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12561 ⟨26,by decide⟩).lower ∧ (cell12561 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12561 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12561 ⟨27,by decide⟩).lower ∧ (cell12561 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12561 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12561 ⟨28,by decide⟩).lower ∧ (cell12561 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12561 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12561 ⟨29,by decide⟩).lower ∧ (cell12561 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12561 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12561 ⟨30,by decide⟩).lower ∧ (cell12561 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12561 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12561 ⟨31,by decide⟩).lower ∧ (cell12561 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12561 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12561 ⟨32,by decide⟩).lower ∧ (cell12561 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12561 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12561 ⟨33,by decide⟩).lower ∧ (cell12561 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12561 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12561 ⟨34,by decide⟩).lower ∧ (cell12561 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12561 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12561 ⟨35,by decide⟩).lower ∧ (cell12561 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12561 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12561 ⟨36,by decide⟩).lower ∧ (cell12561 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12561 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12561 ⟨37,by decide⟩).lower ∧ (cell12561 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12561 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12561 ⟨38,by decide⟩).lower ∧ (cell12561 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12561 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12561 ⟨39,by decide⟩).lower ∧ (cell12561 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12561 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12561 ⟨40,by decide⟩).lower ∧ (cell12561 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12561 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12561 ⟨41,by decide⟩).lower ∧ (cell12561 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12561 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12561 ⟨42,by decide⟩).lower ∧ (cell12561 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12561 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12561 ⟨43,by decide⟩).lower ∧ (cell12561 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12561 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12561 ⟨44,by decide⟩).lower ∧ (cell12561 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12561 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12561 ⟨45,by decide⟩).lower ∧ (cell12561 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12561 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12561 ⟨46,by decide⟩).lower ∧ (cell12561 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12561 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12561 ⟨47,by decide⟩).lower ∧ (cell12561 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12561 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12561 ⟨48,by decide⟩).lower ∧ (cell12561 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12561 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12561 ⟨49,by decide⟩).lower ∧ (cell12561 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12561 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12561 ⟨50,by decide⟩).lower ∧ (cell12561 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12561 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12561 ⟨51,by decide⟩).lower ∧ (cell12561 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12561 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12561 ⟨52,by decide⟩).lower ∧ (cell12561 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12561 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12561 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12561 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12561,cell12561,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12561 i).lower ∧
    (cell12561 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12561 i).upper ≤ (0.532 : ℝ) ∧
    (cell12561 i).centre ≤ (0.1 : ℝ) ∧ (cell12561 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12561 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12561 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12561

/-! The local source numeric instances at 12561 have no network premises. -/
namespace BstLean.Part269.N12561
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12561)
open BstLean.Part268 (cell12561)

noncomputable def sourceNumerics12561 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12561 (cell12561 i)
      scalarRow12561.M scalarRow12561.H scalarRow12561.xi := by
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
    energy_allowance := scalarRow12561.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12561]
    centre_nonneg := (scalarRow12561.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12561])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12561
/-! Actual 12562 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12562 ≤ (1.036007109804 : ℝ) := by
  have hr : (112.080328336421 : ℝ) ≤ √(12562 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.080328336421 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12562 12562 (11 / 1000) ≤
    (0.008528589126 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12562) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.080328336421 : ℝ) ≤ √(12562 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12562)
  have hdiv : K / √(12562 : ℝ) ≤ K / 112.080328336421 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.080328336421 ≤ (0.008528589126 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12562.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12562 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12562 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12562 := gPlus_lower 12562
end BstLean.Part269.N12562

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12562
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036007109803 : ℝ) ≤ wn 12562 := by
  have hn : √(12562 : ℝ) ≤ 112.080328336422 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12562 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.080328336422 ≤ 2 / √(12562 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254696559 : ℝ) ≤ rhoBar 12562 BstLean.Part154.csC ∧
    rhoBar 12562 BstLean.Part154.csC ≤ 0.000254696953 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036007109803 : ℝ) / (1.295212 * 12562) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036007109804 : ℝ) / (1.29521 * 12562) := by gcongr
      _ ≤ (0.000254696953 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12562 BstLean.Part154.csC) ≤ 0.001018852683 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12562 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) ≤ 0.000194539352 ∧
    cc1 (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) ≤ 0.000123786661 ∧
    cc2 (rhoBar 12562 BstLean.Part154.csC) ≤ 0.000071859080 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12562 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12562 BstLean.Part154.csC * nuR (rhoBar 12562 BstLean.Part154.csC)) ≤ 0.000509410124 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254696953 : ℝ) * 0.001018852683 := by gcongr
      _ ≤ (0.000509410124 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12562 BstLean.Part154.csC) * nuR (rhoBar 12562 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001018852683 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12562 BstLean.Part154.csC) * rhoBar 12562 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254696953 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254696953 / 2 + 0.399 * 0.001018852683 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194539352 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000509410124 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123786661 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254696953 / 1.414213562 := by gcongr
      _ ≤ (0.000071859080 : ℝ) := by norm_num

end BstLean.Part269.N12562

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12562
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) ≤ 1.63437E-7 := by
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12562 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12562 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194539352 : ℝ) ^ 2 + 0.000123786661 ^ 2 + 3 * 0.000071859080 ^ 2 +
        2 * 0.797885 * 0.000194539352 * 0.000123786661 + 2 * 0.000194539352 * 0.000071859080 +
        4 * 0.797885 * 0.000123786661 * 0.000071859080 := by gcongr
    _ ≤ (1.63437E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12562 BstLean.Part154.csC Θ ≤ 0.002659194057 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12562 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12562 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036007109804 * 1.63437E-7 / (0.000254696559 : ℝ) := by gcongr
    _ ≤ 0.002659194057 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12562 BstLean.Part154.csC Θ ≤ 0.002951079272 + 0.000671934113 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12562 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036007109804 : ℝ) * ((2 * Θ * 0.000254696953 +
        (6863 / 10000) * 0.000254696953 * 12562 * 0.001018852683) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002951079272 + 0.000671934113 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12562 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12562 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12562 0.011 Θ ∧ gammaRatio 12562 0.011 Θ ≤ 0.000087558227 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12562 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036007109804 : ℝ) * 0.525 / ((1 - 0.011) * 12562) := by gcongr
      _ ≤ (0.000087558227 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12562 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12562 0.011 Θ) :=
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
    badAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000743740740 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12562 BstLean.Part154.csC) 1.22 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 2 (rhoBar 12562 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12562 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12562 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12562 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12562 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12562 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12562 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12562 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12562 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036007109804 : ℝ) * 12562 *
        (2.7751E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000743740740 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003694820012 + 0.003331128170 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12562

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12562
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12562 BstLean.Part154.csC) (piBar (rhoBar 12562 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12562 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12562 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12562 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12562 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12562 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12562 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12562 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12562 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12562 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052774943433 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12562) ≤ 0.010655193457 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12562 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036007109804)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010655193457 + 2 * 0.737676 / 12562) := by gcongr
    _ ≤ (0.052774943433 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12562 12 ≤ 0.0015 := by
  exact BstLean.Part269.S8.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12562

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12562
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497258963 : ℝ) ≤ plow 12562 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12562) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950262302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396076880) : eMP 12562 0.011 xi bn ≤ 0.001201705837 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12562 : ℝ) * (1 - 0.011))) ≤ 0.000594158190 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001396076880 / (12562 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000594158190 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000594158190 : ℝ) + 3.141593 * 0.052950262302 / (12562 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001201705837 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950262302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396076880) : PiBarMP 12562 12 0.011 xi bn ≤ 0.162143551115 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12562 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037364112194 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.462181927324 : ℝ) ≤ √((12562 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.080328336421 : ℝ) ≤ √(12562 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12562) ≤ 0.124307346968 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037364112194 + 0.052950262302 * 1.772454 / (2 * (111.462181927324 : ℝ))) * (1 + 0.001201705837) +
        8 / (12562 * 112.080328336421) + 0.124307346968 := by gcongr
    _ ≤ (0.162143551115 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950262302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396076880) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282884183365) :
    parallelOracle 12562 0.011 xi bn cd ≤ 0.163145539899 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12562 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12562 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497258963 : ℝ) ≤ plow 12562 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.080328336421 : ℝ) ≤ √(12562 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282884183365 : ℝ) / (2 * 0.560497258963 * 112.080328336421)) * 0.162143551115 +
        0.282884183365 ^ 2 / (2 * 0.560497258963 * 112.080328336421) := by gcongr
    _ ≤ (0.163145539899 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052950262302) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001396076880)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282884183365) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12562 12562 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497258963 : ℝ) ≤ plow 12562 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.080328336421 : ℝ) ≤ √(12562 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12562 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12562 Θ 1.22 ≤ 0.011831697138 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.080328336421 := by gcongr <;> linarith
      _ ≤ (0.011831697138 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12562 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12562 12562 0.011 ≤ 0.008528589126 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12562 12562 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12562 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12562 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12562 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12562 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163145539899 + 0.011831697138 + (0.008528589126 : ℝ) *
        (1 + 2 * (0.282884183365 + 0.011831697138) / (0.560497258963 * 112.080328336421))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12562]

end BstLean.Part269.N12562

/-! The original eight local profiles supply actual 12562 moment certificates. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12562 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052950262302 ∧
    0 ≤ bN 12562 BstLean.Part154.csC (groupTheta g) ∧ bN 12562 BstLean.Part154.csC (groupTheta g) ≤ 0.001396076880 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12562 12562 0.011
      (momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12562 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12562 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12562 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230109239932 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12562 0.011
      (momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12562 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12562
/-! The actual computed-centre upper energy formula at 12562. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12562

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12562)
open BstLean.Part268 (cell12562)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085903529294
  | 2 => 0.086854122539
  | 3 => 0.087804039745
  | 4 => 0.088754968809
  | 5 => 0.089708941906
  | 6 => 0.090668385381
  | 7 => 0.091636174115
  | 8 => 0.092615690353
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12562 12562 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12562 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12562

/-! Actual upper energy certificates on all 43 source endpoints at 12562. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12562)
open BstLean.Part268 (cell12562)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12562 (gMinus 12562) (1 - (cell12562 i).lower) ≤ 1 ∧
    energyUpper 12562 (gMinus 12562) (BstLean.Part211.gPlus 12562)
      (finiteEnergy 12562 12562 0.011) (1 - (cell12562 i).lower) ≤
      (cell12562 i).energy := by
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
      have E := BstLean.Part269.S8.uniformEnergy10 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨10,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy11 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨11,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy12 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨12,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy13 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨13,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy14 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨14,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy15 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨15,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy16 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨16,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy17 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨17,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy18 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨18,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy19 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨19,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy20 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨20,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy21 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨21,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy22 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨22,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy23 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨23,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy24 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨24,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy25 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨25,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy26 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨26,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy27 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨27,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy28 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨28,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy29 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨29,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy30 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨30,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy31 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨31,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy32 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨32,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy33 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨33,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy34 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨34,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy35 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨35,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy36 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨36,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy37 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨37,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy38 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨38,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy39 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨39,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy40 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨40,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy41 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨41,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy42 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨42,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy43 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨43,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy44 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨44,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy45 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨45,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy46 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨46,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy47 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨47,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy48 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨48,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy49 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨49,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy50 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨50,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy51 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨51,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S8.uniformEnergy52 (n := 12562) (by norm_num)
        (q := 1 - (cell12562 ⟨52,by decide⟩).lower)
        (by norm_num [cell12562]) (by norm_num [cell12562])
      exact ⟨E.1,E.2.trans (by norm_num [cell12562])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12562

/-! Source-cell containment and simple scalar guards at 12562. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12562)
open BstLean.Part268 (cell12562)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12562 ⟨10,by decide⟩).lower ∧ (cell12562 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12562 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12562 ⟨11,by decide⟩).lower ∧ (cell12562 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12562 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12562 ⟨12,by decide⟩).lower ∧ (cell12562 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12562 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12562 ⟨13,by decide⟩).lower ∧ (cell12562 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12562 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12562 ⟨14,by decide⟩).lower ∧ (cell12562 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12562 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12562 ⟨15,by decide⟩).lower ∧ (cell12562 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12562 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12562 ⟨16,by decide⟩).lower ∧ (cell12562 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12562 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12562 ⟨17,by decide⟩).lower ∧ (cell12562 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12562 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12562 ⟨18,by decide⟩).lower ∧ (cell12562 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12562 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12562 ⟨19,by decide⟩).lower ∧ (cell12562 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12562 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12562 ⟨20,by decide⟩).lower ∧ (cell12562 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12562 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12562 ⟨21,by decide⟩).lower ∧ (cell12562 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12562 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12562 ⟨22,by decide⟩).lower ∧ (cell12562 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12562 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12562 ⟨23,by decide⟩).lower ∧ (cell12562 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12562 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12562 ⟨24,by decide⟩).lower ∧ (cell12562 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12562 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12562 ⟨25,by decide⟩).lower ∧ (cell12562 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12562 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12562 ⟨26,by decide⟩).lower ∧ (cell12562 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12562 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12562 ⟨27,by decide⟩).lower ∧ (cell12562 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12562 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12562 ⟨28,by decide⟩).lower ∧ (cell12562 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12562 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12562 ⟨29,by decide⟩).lower ∧ (cell12562 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12562 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12562 ⟨30,by decide⟩).lower ∧ (cell12562 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12562 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12562 ⟨31,by decide⟩).lower ∧ (cell12562 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12562 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12562 ⟨32,by decide⟩).lower ∧ (cell12562 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12562 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12562 ⟨33,by decide⟩).lower ∧ (cell12562 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12562 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12562 ⟨34,by decide⟩).lower ∧ (cell12562 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12562 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12562 ⟨35,by decide⟩).lower ∧ (cell12562 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12562 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12562 ⟨36,by decide⟩).lower ∧ (cell12562 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12562 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12562 ⟨37,by decide⟩).lower ∧ (cell12562 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12562 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12562 ⟨38,by decide⟩).lower ∧ (cell12562 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12562 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12562 ⟨39,by decide⟩).lower ∧ (cell12562 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12562 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12562 ⟨40,by decide⟩).lower ∧ (cell12562 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12562 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12562 ⟨41,by decide⟩).lower ∧ (cell12562 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12562 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12562 ⟨42,by decide⟩).lower ∧ (cell12562 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12562 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12562 ⟨43,by decide⟩).lower ∧ (cell12562 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12562 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12562 ⟨44,by decide⟩).lower ∧ (cell12562 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12562 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12562 ⟨45,by decide⟩).lower ∧ (cell12562 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12562 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12562 ⟨46,by decide⟩).lower ∧ (cell12562 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12562 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12562 ⟨47,by decide⟩).lower ∧ (cell12562 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12562 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12562 ⟨48,by decide⟩).lower ∧ (cell12562 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12562 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12562 ⟨49,by decide⟩).lower ∧ (cell12562 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12562 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12562 ⟨50,by decide⟩).lower ∧ (cell12562 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12562 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12562 ⟨51,by decide⟩).lower ∧ (cell12562 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12562 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12562 ⟨52,by decide⟩).lower ∧ (cell12562 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12562 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12562 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12562 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12562,cell12562,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12562 i).lower ∧
    (cell12562 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12562 i).upper ≤ (0.532 : ℝ) ∧
    (cell12562 i).centre ≤ (0.1 : ℝ) ∧ (cell12562 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12562 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12562 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12562

/-! The local source numeric instances at 12562 have no network premises. -/
namespace BstLean.Part269.N12562
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12562)
open BstLean.Part268 (cell12562)

noncomputable def sourceNumerics12562 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12562 (cell12562 i)
      scalarRow12562.M scalarRow12562.H scalarRow12562.xi := by
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
    energy_allowance := scalarRow12562.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12562]
    centre_nonneg := (scalarRow12562.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D8.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12562])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12562