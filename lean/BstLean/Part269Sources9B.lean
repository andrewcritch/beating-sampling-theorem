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
import BstLean.Part269Direction9
import BstLean.Part269Shared9
import BstLean.Part269Finite
import BstLean.Part269Rows9
import BstLean.Part269Source
/-! Actual 12588 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12588 ≤ (1.035969576302 : ℝ) := by
  have hr : (112.196256622045 : ℝ) ≤ √(12588 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.196256622045 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12588 12588 (11 / 1000) ≤
    (0.008519776779 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12588) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.196256622045 : ℝ) ≤ √(12588 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12588)
  have hdiv : K / √(12588 : ℝ) ≤ K / 112.196256622045 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.196256622045 ≤ (0.008519776779 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12588.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12588 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12588 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12588 := gPlus_lower 12588
end BstLean.Part269.N12588

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12588
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035969576301 : ℝ) ≤ wn 12588 := by
  have hn : √(12588 : ℝ) ≤ 112.196256622046 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12588 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.196256622046 ≤ 2 / √(12588 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254161285 : ℝ) ≤ rhoBar 12588 BstLean.Part154.csC ∧
    rhoBar 12588 BstLean.Part154.csC ≤ 0.000254161679 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035969576301 : ℝ) / (1.295212 * 12588) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035969576302 : ℝ) / (1.29521 * 12588) := by gcongr
      _ ≤ (0.000254161679 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12588 BstLean.Part154.csC) ≤ 0.001016711315 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12588 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) ≤ 0.000194130487 ∧
    cc1 (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) ≤ 0.000123526501 ∧
    cc2 (rhoBar 12588 BstLean.Part154.csC) ≤ 0.000071708060 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12588 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12588 BstLean.Part154.csC * nuR (rhoBar 12588 BstLean.Part154.csC)) ≤ 0.000508339508 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254161679 : ℝ) * 0.001016711315 := by gcongr
      _ ≤ (0.000508339508 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12588 BstLean.Part154.csC) * nuR (rhoBar 12588 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016711315 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12588 BstLean.Part154.csC) * rhoBar 12588 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254161679 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254161679 / 2 + 0.399 * 0.001016711315 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194130487 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508339508 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123526501 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254161679 / 1.414213562 := by gcongr
      _ ≤ (0.000071708060 : ℝ) := by norm_num

end BstLean.Part269.N12588

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12588
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) ≤ 1.62751E-7 := by
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12588 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12588 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194130487 : ℝ) ^ 2 + 0.000123526501 ^ 2 + 3 * 0.000071708060 ^ 2 +
        2 * 0.797885 * 0.000194130487 * 0.000123526501 + 2 * 0.000194130487 * 0.000071708060 +
        4 * 0.797885 * 0.000123526501 * 0.000071708060 := by gcongr
    _ ≤ (1.62751E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12588 BstLean.Part154.csC Θ ≤ 0.002653513253 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12588 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12588 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035969576302 * 1.62751E-7 / (0.000254161285 : ℝ) := by gcongr
    _ ≤ 0.002653513253 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12588 BstLean.Part154.csC Θ ≤ 0.002944663488 + 0.000670497677 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12588 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035969576302 : ℝ) * ((2 * Θ * 0.000254161679 +
        (6863 / 10000) * 0.000254161679 * 12588 * 0.001016711315) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002944663488 + 0.000670497677 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12588 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12588 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12588 0.011 Θ ∧ gammaRatio 12588 0.011 Θ ≤ 0.000087374213 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12588 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035969576302 : ℝ) * 0.525 / ((1 - 0.011) * 12588) := by gcongr
      _ ≤ (0.000087374213 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12588 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12588 0.011 Θ) :=
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
    badAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12588 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12588 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12588 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12588 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12588 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12588 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12588 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12588 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12588 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12588 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035969576302 : ℝ) * 12588 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003619633010 + 0.003324010930 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12588

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12588
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12588 BstLean.Part154.csC) (piBar (rhoBar 12588 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12588 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12588 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12588 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12588 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12588 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12588 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12588 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12588 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12588 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052719819125 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12588) ≤ 0.010644183835 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12588 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035969576302)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010644183835 + 2 * 0.737676 / 12588) := by gcongr
    _ ≤ (0.052719819125 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12588 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12588

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12588
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498458253 : ℝ) ≤ plow 12588 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12588) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871338749)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393094458) : eMP 12588 0.011 xi bn ≤ 0.001199161762 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12588 : ℝ) * (1 - 0.011))) ≤ 0.000592909938 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393094458 / (12588 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592909938 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592909938 : ℝ) + 3.141593 * 0.052871338749 / (12588 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199161762 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871338749)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393094458) : PiBarMP 12588 12 0.011 xi bn ≤ 0.161973952542 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12588 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037324180608 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.577470844252 : ℝ) ≤ √((12588 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.196256622045 : ℝ) ≤ √(12588 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12588) ≤ 0.124178904736 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037324180608 + 0.052871338749 * 1.772454 / (2 * (111.577470844252 : ℝ))) * (1 + 0.001199161762) +
        8 / (12588 * 112.196256622045) + 0.124178904736 := by gcongr
    _ ≤ (0.161973952542 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871338749)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393094458) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282657503616) :
    parallelOracle 12588 0.011 xi bn cd ≤ 0.162973211197 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12588 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12588 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498458253 : ℝ) ≤ plow 12588 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.196256622045 : ℝ) ≤ √(12588 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282657503616 : ℝ) / (2 * 0.560498458253 * 112.196256622045)) * 0.161973952542 +
        0.282657503616 ^ 2 / (2 * 0.560498458253 * 112.196256622045) := by gcongr
    _ ≤ (0.162973211197 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871338749) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393094458)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282657503616) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12588 12588 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498458253 : ℝ) ≤ plow 12588 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.196256622045 : ℝ) ≤ √(12588 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12588 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12588 Θ 1.22 ≤ 0.011819471879 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.196256622045 := by gcongr <;> linarith
      _ ≤ (0.011819471879 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12588 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12588 12588 0.011 ≤ 0.008519776779 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12588 12588 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12588 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12588 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12588 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12588 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162973211197 + 0.011819471879 + (0.008519776779 : ℝ) *
        (1 + 2 * (0.282657503616 + 0.011819471879) / (0.560498458253 * 112.196256622045))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12588]

end BstLean.Part269.N12588

/-! The original eight local profiles supply actual 12588 moment certificates. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12588 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052871338749 ∧
    0 ≤ bN 12588 BstLean.Part154.csC (groupTheta g) ∧ bN 12588 BstLean.Part154.csC (groupTheta g) ≤ 0.001393094458 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12588 12588 0.011
      (momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12588 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12588 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12588 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229937684491 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12588 0.011
      (momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12588 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12588
/-! The actual computed-centre upper energy formula at 12588. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12588

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12588)
open BstLean.Part268 (cell12588)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085823946352
  | 2 => 0.086772989498
  | 3 => 0.087721116519
  | 4 => 0.088669961067
  | 5 => 0.089621491679
  | 6 => 0.090578060540
  | 7 => 0.091542456651
  | 8 => 0.092517963427
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12588 12588 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12588 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12588

/-! Actual upper energy certificates on all 43 source endpoints at 12588. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12588)
open BstLean.Part268 (cell12588)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12588 (gMinus 12588) (1 - (cell12588 i).lower) ≤ 1 ∧
    energyUpper 12588 (gMinus 12588) (BstLean.Part211.gPlus 12588)
      (finiteEnergy 12588 12588 0.011) (1 - (cell12588 i).lower) ≤
      (cell12588 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨10,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨11,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨12,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨13,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨14,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨15,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨16,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨17,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨18,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨19,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨20,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨21,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨22,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨23,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨24,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨25,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨26,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨27,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨28,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨29,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨30,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨31,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨32,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨33,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨34,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨35,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨36,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨37,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨38,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨39,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨40,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨41,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨42,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨43,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨44,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨45,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨46,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨47,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨48,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨49,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨50,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨51,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12588) (by norm_num)
        (q := 1 - (cell12588 ⟨52,by decide⟩).lower)
        (by norm_num [cell12588]) (by norm_num [cell12588])
      exact ⟨E.1,E.2.trans (by norm_num [cell12588])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12588

/-! Source-cell containment and simple scalar guards at 12588. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12588)
open BstLean.Part268 (cell12588)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12588 ⟨10,by decide⟩).lower ∧ (cell12588 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12588 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12588 ⟨11,by decide⟩).lower ∧ (cell12588 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12588 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12588 ⟨12,by decide⟩).lower ∧ (cell12588 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12588 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12588 ⟨13,by decide⟩).lower ∧ (cell12588 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12588 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12588 ⟨14,by decide⟩).lower ∧ (cell12588 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12588 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12588 ⟨15,by decide⟩).lower ∧ (cell12588 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12588 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12588 ⟨16,by decide⟩).lower ∧ (cell12588 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12588 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12588 ⟨17,by decide⟩).lower ∧ (cell12588 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12588 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12588 ⟨18,by decide⟩).lower ∧ (cell12588 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12588 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12588 ⟨19,by decide⟩).lower ∧ (cell12588 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12588 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12588 ⟨20,by decide⟩).lower ∧ (cell12588 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12588 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12588 ⟨21,by decide⟩).lower ∧ (cell12588 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12588 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12588 ⟨22,by decide⟩).lower ∧ (cell12588 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12588 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12588 ⟨23,by decide⟩).lower ∧ (cell12588 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12588 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12588 ⟨24,by decide⟩).lower ∧ (cell12588 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12588 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12588 ⟨25,by decide⟩).lower ∧ (cell12588 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12588 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12588 ⟨26,by decide⟩).lower ∧ (cell12588 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12588 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12588 ⟨27,by decide⟩).lower ∧ (cell12588 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12588 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12588 ⟨28,by decide⟩).lower ∧ (cell12588 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12588 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12588 ⟨29,by decide⟩).lower ∧ (cell12588 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12588 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12588 ⟨30,by decide⟩).lower ∧ (cell12588 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12588 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12588 ⟨31,by decide⟩).lower ∧ (cell12588 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12588 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12588 ⟨32,by decide⟩).lower ∧ (cell12588 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12588 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12588 ⟨33,by decide⟩).lower ∧ (cell12588 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12588 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12588 ⟨34,by decide⟩).lower ∧ (cell12588 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12588 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12588 ⟨35,by decide⟩).lower ∧ (cell12588 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12588 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12588 ⟨36,by decide⟩).lower ∧ (cell12588 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12588 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12588 ⟨37,by decide⟩).lower ∧ (cell12588 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12588 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12588 ⟨38,by decide⟩).lower ∧ (cell12588 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12588 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12588 ⟨39,by decide⟩).lower ∧ (cell12588 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12588 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12588 ⟨40,by decide⟩).lower ∧ (cell12588 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12588 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12588 ⟨41,by decide⟩).lower ∧ (cell12588 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12588 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12588 ⟨42,by decide⟩).lower ∧ (cell12588 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12588 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12588 ⟨43,by decide⟩).lower ∧ (cell12588 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12588 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12588 ⟨44,by decide⟩).lower ∧ (cell12588 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12588 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12588 ⟨45,by decide⟩).lower ∧ (cell12588 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12588 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12588 ⟨46,by decide⟩).lower ∧ (cell12588 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12588 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12588 ⟨47,by decide⟩).lower ∧ (cell12588 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12588 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12588 ⟨48,by decide⟩).lower ∧ (cell12588 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12588 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12588 ⟨49,by decide⟩).lower ∧ (cell12588 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12588 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12588 ⟨50,by decide⟩).lower ∧ (cell12588 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12588 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12588 ⟨51,by decide⟩).lower ∧ (cell12588 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12588 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12588 ⟨52,by decide⟩).lower ∧ (cell12588 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12588 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12588 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12588 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12588,cell12588,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12588 i).lower ∧
    (cell12588 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12588 i).upper ≤ (0.532 : ℝ) ∧
    (cell12588 i).centre ≤ (0.1 : ℝ) ∧ (cell12588 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12588 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12588 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12588

/-! The local source numeric instances at 12588 have no network premises. -/
namespace BstLean.Part269.N12588
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12588)
open BstLean.Part268 (cell12588)

noncomputable def sourceNumerics12588 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12588 (cell12588 i)
      scalarRow12588.M scalarRow12588.H scalarRow12588.xi := by
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
    energy_allowance := scalarRow12588.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12588]
    centre_nonneg := (scalarRow12588.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12588])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12588
/-! Actual 12589 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12589 ≤ (1.035968135042 : ℝ) := by
  have hr : (112.200713010212 : ℝ) ≤ √(12589 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.200713010212 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12589 12589 (11 / 1000) ≤
    (0.008519438387 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12589) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.200713010212 : ℝ) ≤ √(12589 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12589)
  have hdiv : K / √(12589 : ℝ) ≤ K / 112.200713010212 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.200713010212 ≤ (0.008519438387 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12589.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12589 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12589 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12589 := gPlus_lower 12589
end BstLean.Part269.N12589

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12589
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035968135041 : ℝ) ≤ wn 12589 := by
  have hn : √(12589 : ℝ) ≤ 112.200713010213 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12589 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.200713010213 ≤ 2 / √(12589 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254140743 : ℝ) ≤ rhoBar 12589 BstLean.Part154.csC ∧
    rhoBar 12589 BstLean.Part154.csC ≤ 0.000254141136 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035968135041 : ℝ) / (1.295212 * 12589) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035968135042 : ℝ) / (1.29521 * 12589) := by gcongr
      _ ≤ (0.000254141136 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12589 BstLean.Part154.csC) ≤ 0.001016629132 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12589 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) ≤ 0.000194114795 ∧
    cc1 (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) ≤ 0.000123516516 ∧
    cc2 (rhoBar 12589 BstLean.Part154.csC) ≤ 0.000071702264 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12589 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12589 BstLean.Part154.csC * nuR (rhoBar 12589 BstLean.Part154.csC)) ≤ 0.000508298419 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254141136 : ℝ) * 0.001016629132 := by gcongr
      _ ≤ (0.000508298419 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12589 BstLean.Part154.csC) * nuR (rhoBar 12589 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016629132 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12589 BstLean.Part154.csC) * rhoBar 12589 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254141136 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254141136 / 2 + 0.399 * 0.001016629132 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194114795 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508298419 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123516516 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254141136 / 1.414213562 := by gcongr
      _ ≤ (0.000071702264 : ℝ) := by norm_num

end BstLean.Part269.N12589

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12589
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) ≤ 1.62724E-7 := by
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12589 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12589 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194114795 : ℝ) ^ 2 + 0.000123516516 ^ 2 + 3 * 0.000071702264 ^ 2 +
        2 * 0.797885 * 0.000194114795 * 0.000123516516 + 2 * 0.000194114795 * 0.000071702264 +
        4 * 0.797885 * 0.000123516516 * 0.000071702264 := by gcongr
    _ ≤ (1.62724E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12589 BstLean.Part154.csC Θ ≤ 0.002653283796 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12589 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12589 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035968135042 * 1.62724E-7 / (0.000254140743 : ℝ) := by gcongr
    _ ≤ 0.002653283796 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12589 BstLean.Part154.csC Θ ≤ 0.002944417269 + 0.000670442550 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12589 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035968135042 : ℝ) * ((2 * Θ * 0.000254141136 +
        (6863 / 10000) * 0.000254141136 * 12589 * 0.001016629132) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002944417269 + 0.000670442550 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12589 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12589 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12589 0.011 Θ ∧ gammaRatio 12589 0.011 Θ ≤ 0.000087367151 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12589 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035968135042 : ℝ) * 0.525 / ((1 - 0.011) * 12589) := by gcongr
      _ ≤ (0.000087367151 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12589 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12589 0.011 Θ) :=
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
    badAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12589 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12589 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12589 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12589 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12589 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12589 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12589 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12589 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12589 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12589 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035968135042 : ℝ) * 12589 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003619386791 + 0.003323726346 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12589

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12589
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12589 BstLean.Part154.csC) (piBar (rhoBar 12589 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12589 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12589 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12589 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12589 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12589 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12589 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12589 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12589 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12589 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052717702398 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12589) ≤ 0.010643761070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12589 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035968135042)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010643761070 + 2 * 0.737676 / 12589) := by gcongr
    _ ≤ (0.052717702398 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12589 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12589

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12589
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498504281 : ℝ) ≤ plow 12589 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12589) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870943123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392973993) : eMP 12589 0.011 xi bn ≤ 0.001199062234 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12589 : ℝ) * (1 - 0.011))) ≤ 0.000592860754 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392973993 / (12589 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592860754 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592860754 : ℝ) + 3.141593 * 0.052870943123 / (12589 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199062234 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870943123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392973993) : PiBarMP 12589 12 0.011 xi bn ≤ 0.161967380392 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12589 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037322566807 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.581902654507 : ℝ) ≤ √((12589 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.200713010212 : ℝ) ≤ √(12589 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12589) ≤ 0.124173972598 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037322566807 + 0.052870943123 * 1.772454 / (2 * (111.581902654507 : ℝ))) * (1 + 0.001199062234) +
        8 / (12589 * 112.200713010212) + 0.124173972598 := by gcongr
    _ ≤ (0.161967380392 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870943123)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392973993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282654526598) :
    parallelOracle 12589 0.011 xi bn cd ≤ 0.162966567292 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12589 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12589 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498504281 : ℝ) ≤ plow 12589 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.200713010212 : ℝ) ≤ √(12589 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282654526598 : ℝ) / (2 * 0.560498504281 * 112.200713010212)) * 0.161967380392 +
        0.282654526598 ^ 2 / (2 * 0.560498504281 * 112.200713010212) := by gcongr
    _ ≤ (0.162966567292 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870943123) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392973993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282654526598) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12589 12589 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498504281 : ℝ) ≤ plow 12589 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.200713010212 : ℝ) ≤ √(12589 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12589 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12589 Θ 1.22 ≤ 0.011819002433 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.200713010212 := by gcongr <;> linarith
      _ ≤ (0.011819002433 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12589 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12589 12589 0.011 ≤ 0.008519438387 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12589 12589 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12589 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12589 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12589 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12589 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162966567292 + 0.011819002433 + (0.008519438387 : ℝ) *
        (1 + 2 * (0.282654526598 + 0.011819002433) / (0.560498504281 * 112.200713010212))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12589]

end BstLean.Part269.N12589

/-! The original eight local profiles supply actual 12589 moment certificates. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12589 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052870943123 ∧
    0 ≤ bN 12589 BstLean.Part154.csC (groupTheta g) ∧ bN 12589 BstLean.Part154.csC (groupTheta g) ≤ 0.001392973993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12589 12589 0.011
      (momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12589 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12589 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12589 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229936824200 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12589 0.011
      (momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12589 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12589
/-! The actual computed-centre upper energy formula at 12589. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12589

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12589)
open BstLean.Part268 (cell12589)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085820902033
  | 2 => 0.086769886263
  | 3 => 0.087717945297
  | 4 => 0.088666710737
  | 5 => 0.089618148707
  | 6 => 0.090574608584
  | 7 => 0.091538876117
  | 8 => 0.092514230973
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12589 12589 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12589 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12589

/-! Actual upper energy certificates on all 43 source endpoints at 12589. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12589)
open BstLean.Part268 (cell12589)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12589 (gMinus 12589) (1 - (cell12589 i).lower) ≤ 1 ∧
    energyUpper 12589 (gMinus 12589) (BstLean.Part211.gPlus 12589)
      (finiteEnergy 12589 12589 0.011) (1 - (cell12589 i).lower) ≤
      (cell12589 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨10,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨11,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨12,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨13,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨14,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨15,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨16,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨17,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨18,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨19,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨20,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨21,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨22,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨23,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨24,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨25,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨26,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨27,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨28,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨29,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨30,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨31,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨32,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨33,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨34,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨35,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨36,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨37,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨38,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨39,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨40,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨41,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨42,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨43,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨44,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨45,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨46,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨47,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨48,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨49,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨50,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨51,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12589) (by norm_num)
        (q := 1 - (cell12589 ⟨52,by decide⟩).lower)
        (by norm_num [cell12589]) (by norm_num [cell12589])
      exact ⟨E.1,E.2.trans (by norm_num [cell12589])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12589

/-! Source-cell containment and simple scalar guards at 12589. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12589)
open BstLean.Part268 (cell12589)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12589 ⟨10,by decide⟩).lower ∧ (cell12589 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12589 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12589 ⟨11,by decide⟩).lower ∧ (cell12589 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12589 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12589 ⟨12,by decide⟩).lower ∧ (cell12589 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12589 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12589 ⟨13,by decide⟩).lower ∧ (cell12589 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12589 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12589 ⟨14,by decide⟩).lower ∧ (cell12589 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12589 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12589 ⟨15,by decide⟩).lower ∧ (cell12589 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12589 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12589 ⟨16,by decide⟩).lower ∧ (cell12589 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12589 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12589 ⟨17,by decide⟩).lower ∧ (cell12589 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12589 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12589 ⟨18,by decide⟩).lower ∧ (cell12589 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12589 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12589 ⟨19,by decide⟩).lower ∧ (cell12589 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12589 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12589 ⟨20,by decide⟩).lower ∧ (cell12589 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12589 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12589 ⟨21,by decide⟩).lower ∧ (cell12589 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12589 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12589 ⟨22,by decide⟩).lower ∧ (cell12589 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12589 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12589 ⟨23,by decide⟩).lower ∧ (cell12589 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12589 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12589 ⟨24,by decide⟩).lower ∧ (cell12589 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12589 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12589 ⟨25,by decide⟩).lower ∧ (cell12589 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12589 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12589 ⟨26,by decide⟩).lower ∧ (cell12589 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12589 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12589 ⟨27,by decide⟩).lower ∧ (cell12589 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12589 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12589 ⟨28,by decide⟩).lower ∧ (cell12589 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12589 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12589 ⟨29,by decide⟩).lower ∧ (cell12589 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12589 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12589 ⟨30,by decide⟩).lower ∧ (cell12589 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12589 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12589 ⟨31,by decide⟩).lower ∧ (cell12589 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12589 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12589 ⟨32,by decide⟩).lower ∧ (cell12589 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12589 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12589 ⟨33,by decide⟩).lower ∧ (cell12589 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12589 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12589 ⟨34,by decide⟩).lower ∧ (cell12589 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12589 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12589 ⟨35,by decide⟩).lower ∧ (cell12589 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12589 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12589 ⟨36,by decide⟩).lower ∧ (cell12589 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12589 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12589 ⟨37,by decide⟩).lower ∧ (cell12589 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12589 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12589 ⟨38,by decide⟩).lower ∧ (cell12589 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12589 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12589 ⟨39,by decide⟩).lower ∧ (cell12589 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12589 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12589 ⟨40,by decide⟩).lower ∧ (cell12589 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12589 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12589 ⟨41,by decide⟩).lower ∧ (cell12589 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12589 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12589 ⟨42,by decide⟩).lower ∧ (cell12589 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12589 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12589 ⟨43,by decide⟩).lower ∧ (cell12589 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12589 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12589 ⟨44,by decide⟩).lower ∧ (cell12589 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12589 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12589 ⟨45,by decide⟩).lower ∧ (cell12589 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12589 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12589 ⟨46,by decide⟩).lower ∧ (cell12589 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12589 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12589 ⟨47,by decide⟩).lower ∧ (cell12589 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12589 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12589 ⟨48,by decide⟩).lower ∧ (cell12589 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12589 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12589 ⟨49,by decide⟩).lower ∧ (cell12589 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12589 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12589 ⟨50,by decide⟩).lower ∧ (cell12589 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12589 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12589 ⟨51,by decide⟩).lower ∧ (cell12589 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12589 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12589 ⟨52,by decide⟩).lower ∧ (cell12589 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12589 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12589 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12589 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12589,cell12589,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12589 i).lower ∧
    (cell12589 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12589 i).upper ≤ (0.532 : ℝ) ∧
    (cell12589 i).centre ≤ (0.1 : ℝ) ∧ (cell12589 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12589 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12589 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12589

/-! The local source numeric instances at 12589 have no network premises. -/
namespace BstLean.Part269.N12589
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12589)
open BstLean.Part268 (cell12589)

noncomputable def sourceNumerics12589 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12589 (cell12589 i)
      scalarRow12589.M scalarRow12589.H scalarRow12589.xi := by
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
    energy_allowance := scalarRow12589.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12589]
    centre_nonneg := (scalarRow12589.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12589])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12589
/-! Actual 12590 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12590 ≤ (1.035966693955 : ℝ) := by
  have hr : (112.205169221386 : ℝ) ≤ √(12590 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.205169221386 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12590 12590 (11 / 1000) ≤
    (0.008519100037 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12590) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.205169221386 : ℝ) ≤ √(12590 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12590)
  have hdiv : K / √(12590 : ℝ) ≤ K / 112.205169221386 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.205169221386 ≤ (0.008519100037 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12590.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12590 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12590 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12590 := gPlus_lower 12590
end BstLean.Part269.N12590

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12590
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035966693954 : ℝ) ≤ wn 12590 := by
  have hn : √(12590 : ℝ) ≤ 112.205169221387 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12590 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.205169221387 ≤ 2 / √(12590 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254120203 : ℝ) ≤ rhoBar 12590 BstLean.Part154.csC ∧
    rhoBar 12590 BstLean.Part154.csC ≤ 0.000254120597 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035966693954 : ℝ) / (1.295212 * 12590) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035966693955 : ℝ) / (1.29521 * 12590) := by gcongr
      _ ≤ (0.000254120597 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12590 BstLean.Part154.csC) ≤ 0.001016546966 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12590 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) ≤ 0.000194099107 ∧
    cc1 (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) ≤ 0.000123506534 ∧
    cc2 (rhoBar 12590 BstLean.Part154.csC) ≤ 0.000071696469 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12590 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12590 BstLean.Part154.csC * nuR (rhoBar 12590 BstLean.Part154.csC)) ≤ 0.000508257339 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254120597 : ℝ) * 0.001016546966 := by gcongr
      _ ≤ (0.000508257339 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12590 BstLean.Part154.csC) * nuR (rhoBar 12590 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016546966 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12590 BstLean.Part154.csC) * rhoBar 12590 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254120597 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254120597 / 2 + 0.399 * 0.001016546966 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194099107 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508257339 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123506534 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254120597 / 1.414213562 := by gcongr
      _ ≤ (0.000071696469 : ℝ) := by norm_num

end BstLean.Part269.N12590

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12590
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) ≤ 1.62698E-7 := by
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12590 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12590 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194099107 : ℝ) ^ 2 + 0.000123506534 ^ 2 + 3 * 0.000071696469 ^ 2 +
        2 * 0.797885 * 0.000194099107 * 0.000123506534 + 2 * 0.000194099107 * 0.000071696469 +
        4 * 0.797885 * 0.000123506534 * 0.000071696469 := by gcongr
    _ ≤ (1.62698E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12590 BstLean.Part154.csC Θ ≤ 0.002653070590 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12590 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12590 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035966693955 * 1.62698E-7 / (0.000254120203 : ℝ) := by gcongr
    _ ≤ 0.002653070590 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12590 BstLean.Part154.csC Θ ≤ 0.002944171109 + 0.000670387434 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12590 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035966693955 : ℝ) * ((2 * Θ * 0.000254120597 +
        (6863 / 10000) * 0.000254120597 * 12590 * 0.001016546966) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002944171109 + 0.000670387434 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12590 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12590 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12590 0.011 Θ ∧ gammaRatio 12590 0.011 Θ ≤ 0.000087360090 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12590 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035966693955 : ℝ) * 0.525 / ((1 - 0.011) * 12590) := by gcongr
      _ ≤ (0.000087360090 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12590 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12590 0.011 Θ) :=
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
    badAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12590 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12590 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12590 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12590 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12590 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12590 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12590 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12590 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12590 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12590 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035966693955 : ℝ) * 12590 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003619140631 + 0.003323458024 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12590

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12590
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12590 BstLean.Part154.csC) (piBar (rhoBar 12590 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12590 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12590 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12590 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12590 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12590 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12590 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12590 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12590 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12590 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052715585919 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12590) ≤ 0.010643338354 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12590 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035966693955)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010643338354 + 2 * 0.737676 / 12590) := by gcongr
    _ ≤ (0.052715585919 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12590 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12590

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12590
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498550301 : ℝ) ≤ plow 12590 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12590) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870556094)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392862060) : eMP 12590 0.011 xi bn ≤ 0.001198966349 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12590 : ℝ) * (1 - 0.011))) ≤ 0.000592813390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392862060 / (12590 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592813390 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592813390 : ℝ) + 3.141593 * 0.052870556094 / (12590 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198966349 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870556094)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392862060) : PiBarMP 12590 12 0.011 xi bn ≤ 0.161960923409 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12590 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037321067241 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.586334288747 : ℝ) ≤ √((12590 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.205169221386 : ℝ) ≤ √(12590 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12590) ≤ 0.124169041048 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037321067241 + 0.052870556094 * 1.772454 / (2 * (111.586334288747 : ℝ))) * (1 + 0.001198966349) +
        8 / (12590 * 112.205169221386) + 0.124169041048 := by gcongr
    _ ≤ (0.161960923409 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870556094)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392862060) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282651568519) :
    parallelOracle 12590 0.011 xi bn cd ≤ 0.162960038931 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12590 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12590 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498550301 : ℝ) ≤ plow 12590 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.205169221386 : ℝ) ≤ √(12590 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282651568519 : ℝ) / (2 * 0.560498550301 * 112.205169221386)) * 0.161960923409 +
        0.282651568519 ^ 2 / (2 * 0.560498550301 * 112.205169221386) := by gcongr
    _ ≤ (0.162960038931 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870556094) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392862060)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282651568519) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12590 12590 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498550301 : ℝ) ≤ plow 12590 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.205169221386 : ℝ) ≤ √(12590 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12590 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12590 Θ 1.22 ≤ 0.011818533043 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.205169221386 := by gcongr <;> linarith
      _ ≤ (0.011818533043 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12590 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12590 12590 0.011 ≤ 0.008519100037 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12590 12590 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12590 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12590 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12590 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12590 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162960038931 + 0.011818533043 + (0.008519100037 : ℝ) *
        (1 + 2 * (0.282651568519 + 0.011818533043) / (0.560498550301 * 112.205169221386))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12590]

end BstLean.Part269.N12590

/-! The original eight local profiles supply actual 12590 moment certificates. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12590 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052870556094 ∧
    0 ≤ bN 12590 BstLean.Part154.csC (groupTheta g) ∧ bN 12590 BstLean.Part154.csC (groupTheta g) ≤ 0.001392862060 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12590 12590 0.011
      (momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12590 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12590 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12590 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229935982600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12590 0.011
      (momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12590 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12590
/-! The actual computed-centre upper energy formula at 12590. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12590

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12590)
open BstLean.Part268 (cell12590)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085817858929
  | 2 => 0.086766784293
  | 3 => 0.087714775405
  | 4 => 0.088663461814
  | 5 => 0.089614807238
  | 6 => 0.090571158247
  | 7 => 0.091535297341
  | 8 => 0.092510500444
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12590 12590 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12590 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12590

/-! Actual upper energy certificates on all 43 source endpoints at 12590. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12590)
open BstLean.Part268 (cell12590)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12590 (gMinus 12590) (1 - (cell12590 i).lower) ≤ 1 ∧
    energyUpper 12590 (gMinus 12590) (BstLean.Part211.gPlus 12590)
      (finiteEnergy 12590 12590 0.011) (1 - (cell12590 i).lower) ≤
      (cell12590 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨10,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨11,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨12,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨13,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨14,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨15,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨16,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨17,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨18,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨19,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨20,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨21,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨22,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨23,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨24,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨25,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨26,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨27,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨28,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨29,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨30,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨31,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨32,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨33,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨34,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨35,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨36,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨37,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨38,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨39,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨40,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨41,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨42,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨43,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨44,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨45,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨46,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨47,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨48,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨49,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨50,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨51,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12590) (by norm_num)
        (q := 1 - (cell12590 ⟨52,by decide⟩).lower)
        (by norm_num [cell12590]) (by norm_num [cell12590])
      exact ⟨E.1,E.2.trans (by norm_num [cell12590])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12590

/-! Source-cell containment and simple scalar guards at 12590. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12590)
open BstLean.Part268 (cell12590)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12590 ⟨10,by decide⟩).lower ∧ (cell12590 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12590 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12590 ⟨11,by decide⟩).lower ∧ (cell12590 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12590 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12590 ⟨12,by decide⟩).lower ∧ (cell12590 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12590 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12590 ⟨13,by decide⟩).lower ∧ (cell12590 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12590 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12590 ⟨14,by decide⟩).lower ∧ (cell12590 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12590 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12590 ⟨15,by decide⟩).lower ∧ (cell12590 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12590 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12590 ⟨16,by decide⟩).lower ∧ (cell12590 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12590 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12590 ⟨17,by decide⟩).lower ∧ (cell12590 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12590 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12590 ⟨18,by decide⟩).lower ∧ (cell12590 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12590 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12590 ⟨19,by decide⟩).lower ∧ (cell12590 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12590 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12590 ⟨20,by decide⟩).lower ∧ (cell12590 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12590 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12590 ⟨21,by decide⟩).lower ∧ (cell12590 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12590 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12590 ⟨22,by decide⟩).lower ∧ (cell12590 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12590 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12590 ⟨23,by decide⟩).lower ∧ (cell12590 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12590 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12590 ⟨24,by decide⟩).lower ∧ (cell12590 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12590 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12590 ⟨25,by decide⟩).lower ∧ (cell12590 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12590 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12590 ⟨26,by decide⟩).lower ∧ (cell12590 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12590 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12590 ⟨27,by decide⟩).lower ∧ (cell12590 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12590 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12590 ⟨28,by decide⟩).lower ∧ (cell12590 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12590 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12590 ⟨29,by decide⟩).lower ∧ (cell12590 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12590 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12590 ⟨30,by decide⟩).lower ∧ (cell12590 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12590 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12590 ⟨31,by decide⟩).lower ∧ (cell12590 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12590 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12590 ⟨32,by decide⟩).lower ∧ (cell12590 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12590 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12590 ⟨33,by decide⟩).lower ∧ (cell12590 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12590 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12590 ⟨34,by decide⟩).lower ∧ (cell12590 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12590 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12590 ⟨35,by decide⟩).lower ∧ (cell12590 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12590 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12590 ⟨36,by decide⟩).lower ∧ (cell12590 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12590 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12590 ⟨37,by decide⟩).lower ∧ (cell12590 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12590 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12590 ⟨38,by decide⟩).lower ∧ (cell12590 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12590 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12590 ⟨39,by decide⟩).lower ∧ (cell12590 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12590 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12590 ⟨40,by decide⟩).lower ∧ (cell12590 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12590 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12590 ⟨41,by decide⟩).lower ∧ (cell12590 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12590 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12590 ⟨42,by decide⟩).lower ∧ (cell12590 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12590 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12590 ⟨43,by decide⟩).lower ∧ (cell12590 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12590 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12590 ⟨44,by decide⟩).lower ∧ (cell12590 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12590 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12590 ⟨45,by decide⟩).lower ∧ (cell12590 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12590 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12590 ⟨46,by decide⟩).lower ∧ (cell12590 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12590 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12590 ⟨47,by decide⟩).lower ∧ (cell12590 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12590 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12590 ⟨48,by decide⟩).lower ∧ (cell12590 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12590 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12590 ⟨49,by decide⟩).lower ∧ (cell12590 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12590 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12590 ⟨50,by decide⟩).lower ∧ (cell12590 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12590 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12590 ⟨51,by decide⟩).lower ∧ (cell12590 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12590 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12590 ⟨52,by decide⟩).lower ∧ (cell12590 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12590 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12590 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12590 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12590,cell12590,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12590 i).lower ∧
    (cell12590 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12590 i).upper ≤ (0.532 : ℝ) ∧
    (cell12590 i).centre ≤ (0.1 : ℝ) ∧ (cell12590 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12590 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12590 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12590

/-! The local source numeric instances at 12590 have no network premises. -/
namespace BstLean.Part269.N12590
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12590)
open BstLean.Part268 (cell12590)

noncomputable def sourceNumerics12590 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12590 (cell12590 i)
      scalarRow12590.M scalarRow12590.H scalarRow12590.xi := by
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
    energy_allowance := scalarRow12590.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12590]
    centre_nonneg := (scalarRow12590.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12590])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12590
/-! Actual 12591 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12591 ≤ (1.035965253040 : ℝ) := by
  have hr : (112.209625255590 : ℝ) ≤ √(12591 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.209625255590 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12591 12591 (11 / 1000) ≤
    (0.008518761726 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12591) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.209625255590 : ℝ) ≤ √(12591 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12591)
  have hdiv : K / √(12591 : ℝ) ≤ K / 112.209625255590 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.209625255590 ≤ (0.008518761726 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12591.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12591 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12591 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12591 := gPlus_lower 12591
end BstLean.Part269.N12591

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12591
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035965253039 : ℝ) ≤ wn 12591 := by
  have hn : √(12591 : ℝ) ≤ 112.209625255591 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12591 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.209625255591 ≤ 2 / √(12591 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254099667 : ℝ) ≤ rhoBar 12591 BstLean.Part154.csC ∧
    rhoBar 12591 BstLean.Part154.csC ≤ 0.000254100061 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035965253039 : ℝ) / (1.295212 * 12591) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035965253040 : ℝ) / (1.29521 * 12591) := by gcongr
      _ ≤ (0.000254100061 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12591 BstLean.Part154.csC) ≤ 0.001016464811 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12591 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) ≤ 0.000194083420 ∧
    cc1 (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) ≤ 0.000123496553 ∧
    cc2 (rhoBar 12591 BstLean.Part154.csC) ≤ 0.000071690675 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12591 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12591 BstLean.Part154.csC * nuR (rhoBar 12591 BstLean.Part154.csC)) ≤ 0.000508216264 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254100061 : ℝ) * 0.001016464811 := by gcongr
      _ ≤ (0.000508216264 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12591 BstLean.Part154.csC) * nuR (rhoBar 12591 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016464811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12591 BstLean.Part154.csC) * rhoBar 12591 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254100061 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254100061 / 2 + 0.399 * 0.001016464811 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194083420 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508216264 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123496553 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254100061 / 1.414213562 := by gcongr
      _ ≤ (0.000071690675 : ℝ) := by norm_num

end BstLean.Part269.N12591

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12591
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) ≤ 1.62672E-7 := by
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12591 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12591 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194083420 : ℝ) ^ 2 + 0.000123496553 ^ 2 + 3 * 0.000071690675 ^ 2 +
        2 * 0.797885 * 0.000194083420 * 0.000123496553 + 2 * 0.000194083420 * 0.000071690675 +
        4 * 0.797885 * 0.000123496553 * 0.000071690675 := by gcongr
    _ ≤ (1.62672E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12591 BstLean.Part154.csC Θ ≤ 0.002652857309 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12591 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12591 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035965253040 * 1.62672E-7 / (0.000254099667 : ℝ) := by gcongr
    _ ≤ 0.002652857309 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12591 BstLean.Part154.csC Θ ≤ 0.002943924980 + 0.000670332326 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12591 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035965253040 : ℝ) * ((2 * Θ * 0.000254100061 +
        (6863 / 10000) * 0.000254100061 * 12591 * 0.001016464811) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002943924980 + 0.000670332326 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12591 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12591 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12591 0.011 Θ ∧ gammaRatio 12591 0.011 Θ ≤ 0.000087353030 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12591 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035965253040 : ℝ) * 0.525 / ((1 - 0.011) * 12591) := by gcongr
      _ ≤ (0.000087353030 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12591 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12591 0.011 Θ) :=
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
    badAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12591 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12591 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12591 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12591 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12591 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12591 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12591 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12591 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12591 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12591 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035965253040 : ℝ) * 12591 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003618894502 + 0.003323189635 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12591

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12591
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12591 BstLean.Part154.csC) (piBar (rhoBar 12591 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12591 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12591 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12591 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12591 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12591 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12591 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12591 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12591 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12591 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052713469697 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12591) ≤ 0.010642915689 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12591 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035965253040)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010642915689 + 2 * 0.737676 / 12591) := by gcongr
    _ ≤ (0.052713469697 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12591 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12591

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12591
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498596314 : ℝ) ≤ plow 12591 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12591) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870169061)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392750088) : eMP 12591 0.011 xi bn ≤ 0.001198870452 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12591 : ℝ) * (1 - 0.011))) ≤ 0.000592766020 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392750088 / (12591 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592766020 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592766020 : ℝ) + 3.141593 * 0.052870169061 / (12591 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198870452 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870169061)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392750088) : PiBarMP 12591 12 0.011 xi bn ≤ 0.161954466433 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12591 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037319567093 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.590765746991 : ℝ) ≤ √((12591 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.209625255590 : ℝ) ≤ √(12591 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12591) ≤ 0.124164110085 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037319567093 + 0.052870169061 * 1.772454 / (2 * (111.590765746991 : ℝ))) * (1 + 0.001198870452) +
        8 / (12591 * 112.209625255590) + 0.124164110085 := by gcongr
    _ ≤ (0.161954466433 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870169061)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392750088) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282648610685) :
    parallelOracle 12591 0.011 xi bn cd ≤ 0.162953510586 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12591 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12591 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498596314 : ℝ) ≤ plow 12591 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.209625255590 : ℝ) ≤ √(12591 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282648610685 : ℝ) / (2 * 0.560498596314 * 112.209625255590)) * 0.161954466433 +
        0.282648610685 ^ 2 / (2 * 0.560498596314 * 112.209625255590) := by gcongr
    _ ≤ (0.162953510586 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052870169061) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392750088)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282648610685) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12591 12591 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498596314 : ℝ) ≤ plow 12591 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.209625255590 : ℝ) ≤ √(12591 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12591 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12591 Θ 1.22 ≤ 0.011818063709 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.209625255590 := by gcongr <;> linarith
      _ ≤ (0.011818063709 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12591 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12591 12591 0.011 ≤ 0.008518761726 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12591 12591 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12591 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12591 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12591 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12591 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162953510586 + 0.011818063709 + (0.008518761726 : ℝ) *
        (1 + 2 * (0.282648610685 + 0.011818063709) / (0.560498596314 * 112.209625255590))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12591]

end BstLean.Part269.N12591

/-! The original eight local profiles supply actual 12591 moment certificates. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12591 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052870169061 ∧
    0 ≤ bN 12591 BstLean.Part154.csC (groupTheta g) ∧ bN 12591 BstLean.Part154.csC (groupTheta g) ≤ 0.001392750088 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12591 12591 0.011
      (momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12591 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12591 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12591 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229935140988 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12591 0.011
      (momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12591 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12591
/-! The actual computed-centre upper energy formula at 12591. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12591

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12591)
open BstLean.Part268 (cell12591)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085814817039
  | 2 => 0.086763683589
  | 3 => 0.087711606842
  | 4 => 0.088660214297
  | 5 => 0.089611467270
  | 6 => 0.090567709527
  | 7 => 0.091531720321
  | 8 => 0.092506771840
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12591 12591 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12591 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12591

/-! Actual upper energy certificates on all 43 source endpoints at 12591. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12591)
open BstLean.Part268 (cell12591)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12591 (gMinus 12591) (1 - (cell12591 i).lower) ≤ 1 ∧
    energyUpper 12591 (gMinus 12591) (BstLean.Part211.gPlus 12591)
      (finiteEnergy 12591 12591 0.011) (1 - (cell12591 i).lower) ≤
      (cell12591 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨10,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨11,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨12,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨13,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨14,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨15,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨16,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨17,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨18,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨19,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨20,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨21,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨22,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨23,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨24,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨25,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨26,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨27,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨28,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨29,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨30,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨31,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨32,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨33,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨34,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨35,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨36,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨37,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨38,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨39,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨40,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨41,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨42,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨43,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨44,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨45,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨46,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨47,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨48,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨49,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨50,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨51,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12591) (by norm_num)
        (q := 1 - (cell12591 ⟨52,by decide⟩).lower)
        (by norm_num [cell12591]) (by norm_num [cell12591])
      exact ⟨E.1,E.2.trans (by norm_num [cell12591])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12591

/-! Source-cell containment and simple scalar guards at 12591. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12591)
open BstLean.Part268 (cell12591)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12591 ⟨10,by decide⟩).lower ∧ (cell12591 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12591 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12591 ⟨11,by decide⟩).lower ∧ (cell12591 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12591 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12591 ⟨12,by decide⟩).lower ∧ (cell12591 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12591 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12591 ⟨13,by decide⟩).lower ∧ (cell12591 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12591 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12591 ⟨14,by decide⟩).lower ∧ (cell12591 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12591 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12591 ⟨15,by decide⟩).lower ∧ (cell12591 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12591 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12591 ⟨16,by decide⟩).lower ∧ (cell12591 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12591 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12591 ⟨17,by decide⟩).lower ∧ (cell12591 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12591 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12591 ⟨18,by decide⟩).lower ∧ (cell12591 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12591 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12591 ⟨19,by decide⟩).lower ∧ (cell12591 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12591 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12591 ⟨20,by decide⟩).lower ∧ (cell12591 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12591 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12591 ⟨21,by decide⟩).lower ∧ (cell12591 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12591 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12591 ⟨22,by decide⟩).lower ∧ (cell12591 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12591 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12591 ⟨23,by decide⟩).lower ∧ (cell12591 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12591 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12591 ⟨24,by decide⟩).lower ∧ (cell12591 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12591 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12591 ⟨25,by decide⟩).lower ∧ (cell12591 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12591 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12591 ⟨26,by decide⟩).lower ∧ (cell12591 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12591 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12591 ⟨27,by decide⟩).lower ∧ (cell12591 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12591 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12591 ⟨28,by decide⟩).lower ∧ (cell12591 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12591 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12591 ⟨29,by decide⟩).lower ∧ (cell12591 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12591 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12591 ⟨30,by decide⟩).lower ∧ (cell12591 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12591 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12591 ⟨31,by decide⟩).lower ∧ (cell12591 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12591 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12591 ⟨32,by decide⟩).lower ∧ (cell12591 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12591 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12591 ⟨33,by decide⟩).lower ∧ (cell12591 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12591 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12591 ⟨34,by decide⟩).lower ∧ (cell12591 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12591 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12591 ⟨35,by decide⟩).lower ∧ (cell12591 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12591 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12591 ⟨36,by decide⟩).lower ∧ (cell12591 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12591 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12591 ⟨37,by decide⟩).lower ∧ (cell12591 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12591 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12591 ⟨38,by decide⟩).lower ∧ (cell12591 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12591 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12591 ⟨39,by decide⟩).lower ∧ (cell12591 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12591 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12591 ⟨40,by decide⟩).lower ∧ (cell12591 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12591 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12591 ⟨41,by decide⟩).lower ∧ (cell12591 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12591 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12591 ⟨42,by decide⟩).lower ∧ (cell12591 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12591 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12591 ⟨43,by decide⟩).lower ∧ (cell12591 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12591 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12591 ⟨44,by decide⟩).lower ∧ (cell12591 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12591 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12591 ⟨45,by decide⟩).lower ∧ (cell12591 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12591 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12591 ⟨46,by decide⟩).lower ∧ (cell12591 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12591 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12591 ⟨47,by decide⟩).lower ∧ (cell12591 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12591 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12591 ⟨48,by decide⟩).lower ∧ (cell12591 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12591 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12591 ⟨49,by decide⟩).lower ∧ (cell12591 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12591 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12591 ⟨50,by decide⟩).lower ∧ (cell12591 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12591 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12591 ⟨51,by decide⟩).lower ∧ (cell12591 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12591 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12591 ⟨52,by decide⟩).lower ∧ (cell12591 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12591 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12591 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12591 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12591,cell12591,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12591 i).lower ∧
    (cell12591 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12591 i).upper ≤ (0.532 : ℝ) ∧
    (cell12591 i).centre ≤ (0.1 : ℝ) ∧ (cell12591 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12591 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12591 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12591

/-! The local source numeric instances at 12591 have no network premises. -/
namespace BstLean.Part269.N12591
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12591)
open BstLean.Part268 (cell12591)

noncomputable def sourceNumerics12591 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12591 (cell12591 i)
      scalarRow12591.M scalarRow12591.H scalarRow12591.xi := by
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
    energy_allowance := scalarRow12591.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12591]
    centre_nonneg := (scalarRow12591.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12591])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12591
/-! Actual 12592 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12592 ≤ (1.035963812298 : ℝ) := by
  have hr : (112.214081112844 : ℝ) ≤ √(12592 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.214081112844 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12592 12592 (11 / 1000) ≤
    (0.008518423456 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12592) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.214081112844 : ℝ) ≤ √(12592 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12592)
  have hdiv : K / √(12592 : ℝ) ≤ K / 112.214081112844 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.214081112844 ≤ (0.008518423456 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12592.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12592 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12592 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12592 := gPlus_lower 12592
end BstLean.Part269.N12592

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12592
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035963812297 : ℝ) ≤ wn 12592 := by
  have hn : √(12592 : ℝ) ≤ 112.214081112845 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12592 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.214081112845 ≤ 2 / √(12592 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254079134 : ℝ) ≤ rhoBar 12592 BstLean.Part154.csC ∧
    rhoBar 12592 BstLean.Part154.csC ≤ 0.000254079528 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035963812297 : ℝ) / (1.295212 * 12592) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035963812298 : ℝ) / (1.29521 * 12592) := by gcongr
      _ ≤ (0.000254079528 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12592 BstLean.Part154.csC) ≤ 0.001016382669 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12592 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) ≤ 0.000194067736 ∧
    cc1 (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) ≤ 0.000123486573 ∧
    cc2 (rhoBar 12592 BstLean.Part154.csC) ≤ 0.000071684882 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12592 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12592 BstLean.Part154.csC * nuR (rhoBar 12592 BstLean.Part154.csC)) ≤ 0.000508175195 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254079528 : ℝ) * 0.001016382669 := by gcongr
      _ ≤ (0.000508175195 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12592 BstLean.Part154.csC) * nuR (rhoBar 12592 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016382669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12592 BstLean.Part154.csC) * rhoBar 12592 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254079528 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254079528 / 2 + 0.399 * 0.001016382669 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194067736 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508175195 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123486573 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254079528 / 1.414213562 := by gcongr
      _ ≤ (0.000071684882 : ℝ) := by norm_num

end BstLean.Part269.N12592

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12592
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) ≤ 1.62645E-7 := by
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12592 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12592 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194067736 : ℝ) ^ 2 + 0.000123486573 ^ 2 + 3 * 0.000071684882 ^ 2 +
        2 * 0.797885 * 0.000194067736 * 0.000123486573 + 2 * 0.000194067736 * 0.000071684882 +
        4 * 0.797885 * 0.000123486573 * 0.000071684882 := by gcongr
    _ ≤ (1.62645E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12592 BstLean.Part154.csC Θ ≤ 0.002652627654 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12592 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12592 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035963812298 * 1.62645E-7 / (0.000254079134 : ℝ) := by gcongr
    _ ≤ 0.002652627654 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12592 BstLean.Part154.csC Θ ≤ 0.002943678888 + 0.000670277227 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12592 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035963812298 : ℝ) * ((2 * Θ * 0.000254079528 +
        (6863 / 10000) * 0.000254079528 * 12592 * 0.001016382669) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002943678888 + 0.000670277227 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12592 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12592 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12592 0.011 Θ ∧ gammaRatio 12592 0.011 Θ ≤ 0.000087345972 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12592 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035963812298 : ℝ) * 0.525 / ((1 - 0.011) * 12592) := by gcongr
      _ ≤ (0.000087345972 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12592 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12592 0.011 Θ) :=
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
    badAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12592 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12592 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12592 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12592 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12592 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12592 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12592 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12592 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12592 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12592 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035963812298 : ℝ) * 12592 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003618648410 + 0.003322904881 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12592

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12592
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12592 BstLean.Part154.csC) (piBar (rhoBar 12592 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12592 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12592 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12592 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12592 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12592 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12592 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12592 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12592 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12592 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052711353732 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12592) ≤ 0.010642493075 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12592 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035963812298)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010642493075 + 2 * 0.737676 / 12592) := by gcongr
    _ ≤ (0.052711353732 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12592 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12592

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12592
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498642320 : ℝ) ≤ plow 12592 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12592) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869773473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392629519) : eMP 12592 0.011 xi bn ≤ 0.001198770903 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12592 : ℝ) * (1 - 0.011))) ≤ 0.000592716825 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392629519 / (12592 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592716825 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592716825 : ℝ) + 3.141593 * 0.052869773473 / (12592 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198770903 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869773473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392629519) : PiBarMP 12592 12 0.011 xi bn ≤ 0.161947894457 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12592 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037317951699 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.595197029262 : ℝ) ≤ √((12592 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.214081112844 : ℝ) ≤ √(12592 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12592) ≤ 0.124159179709 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037317951699 + 0.052869773473 * 1.772454 / (2 * (111.595197029262 : ℝ))) * (1 + 0.001198770903) +
        8 / (12592 * 112.214081112844) + 0.124159179709 := by gcongr
    _ ≤ (0.161947894457 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869773473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392629519) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282645634502) :
    parallelOracle 12592 0.011 xi bn cd ≤ 0.162946866884 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12592 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12592 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498642320 : ℝ) ≤ plow 12592 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.214081112844 : ℝ) ≤ √(12592 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282645634502 : ℝ) / (2 * 0.560498642320 * 112.214081112844)) * 0.161947894457 +
        0.282645634502 ^ 2 / (2 * 0.560498642320 * 112.214081112844) := by gcongr
    _ ≤ (0.162946866884 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869773473) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392629519)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282645634502) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12592 12592 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498642320 : ℝ) ≤ plow 12592 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.214081112844 : ℝ) ≤ √(12592 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12592 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12592 Θ 1.22 ≤ 0.011817594431 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.214081112844 := by gcongr <;> linarith
      _ ≤ (0.011817594431 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12592 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12592 12592 0.011 ≤ 0.008518423456 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12592 12592 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12592 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12592 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12592 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12592 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162946866884 + 0.011817594431 + (0.008518423456 : ℝ) *
        (1 + 2 * (0.282645634502 + 0.011817594431) / (0.560498642320 * 112.214081112844))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12592]

end BstLean.Part269.N12592

/-! The original eight local profiles supply actual 12592 moment certificates. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12592 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052869773473 ∧
    0 ≤ bN 12592 BstLean.Part154.csC (groupTheta g) ∧ bN 12592 BstLean.Part154.csC (groupTheta g) ≤ 0.001392629519 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12592 12592 0.011
      (momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12592 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12592 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12592 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229934280770 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12592 0.011
      (momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12592 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12592
/-! The actual computed-centre upper energy formula at 12592. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12592

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12592)
open BstLean.Part268 (cell12592)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085811776361
  | 2 => 0.086760584149
  | 3 => 0.087708439605
  | 4 => 0.088656968185
  | 5 => 0.089608128801
  | 6 => 0.090564262422
  | 7 => 0.091528145056
  | 8 => 0.092503045156
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12592 12592 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12592 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12592

/-! Actual upper energy certificates on all 43 source endpoints at 12592. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12592)
open BstLean.Part268 (cell12592)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12592 (gMinus 12592) (1 - (cell12592 i).lower) ≤ 1 ∧
    energyUpper 12592 (gMinus 12592) (BstLean.Part211.gPlus 12592)
      (finiteEnergy 12592 12592 0.011) (1 - (cell12592 i).lower) ≤
      (cell12592 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨10,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨11,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨12,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨13,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨14,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨15,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨16,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨17,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨18,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨19,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨20,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨21,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨22,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨23,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨24,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨25,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨26,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨27,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨28,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨29,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨30,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨31,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨32,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨33,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨34,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨35,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨36,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨37,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨38,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨39,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨40,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨41,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨42,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨43,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨44,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨45,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨46,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨47,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨48,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨49,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨50,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨51,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12592) (by norm_num)
        (q := 1 - (cell12592 ⟨52,by decide⟩).lower)
        (by norm_num [cell12592]) (by norm_num [cell12592])
      exact ⟨E.1,E.2.trans (by norm_num [cell12592])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12592

/-! Source-cell containment and simple scalar guards at 12592. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12592)
open BstLean.Part268 (cell12592)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12592 ⟨10,by decide⟩).lower ∧ (cell12592 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12592 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12592 ⟨11,by decide⟩).lower ∧ (cell12592 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12592 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12592 ⟨12,by decide⟩).lower ∧ (cell12592 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12592 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12592 ⟨13,by decide⟩).lower ∧ (cell12592 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12592 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12592 ⟨14,by decide⟩).lower ∧ (cell12592 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12592 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12592 ⟨15,by decide⟩).lower ∧ (cell12592 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12592 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12592 ⟨16,by decide⟩).lower ∧ (cell12592 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12592 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12592 ⟨17,by decide⟩).lower ∧ (cell12592 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12592 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12592 ⟨18,by decide⟩).lower ∧ (cell12592 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12592 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12592 ⟨19,by decide⟩).lower ∧ (cell12592 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12592 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12592 ⟨20,by decide⟩).lower ∧ (cell12592 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12592 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12592 ⟨21,by decide⟩).lower ∧ (cell12592 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12592 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12592 ⟨22,by decide⟩).lower ∧ (cell12592 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12592 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12592 ⟨23,by decide⟩).lower ∧ (cell12592 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12592 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12592 ⟨24,by decide⟩).lower ∧ (cell12592 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12592 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12592 ⟨25,by decide⟩).lower ∧ (cell12592 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12592 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12592 ⟨26,by decide⟩).lower ∧ (cell12592 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12592 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12592 ⟨27,by decide⟩).lower ∧ (cell12592 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12592 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12592 ⟨28,by decide⟩).lower ∧ (cell12592 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12592 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12592 ⟨29,by decide⟩).lower ∧ (cell12592 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12592 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12592 ⟨30,by decide⟩).lower ∧ (cell12592 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12592 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12592 ⟨31,by decide⟩).lower ∧ (cell12592 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12592 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12592 ⟨32,by decide⟩).lower ∧ (cell12592 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12592 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12592 ⟨33,by decide⟩).lower ∧ (cell12592 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12592 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12592 ⟨34,by decide⟩).lower ∧ (cell12592 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12592 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12592 ⟨35,by decide⟩).lower ∧ (cell12592 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12592 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12592 ⟨36,by decide⟩).lower ∧ (cell12592 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12592 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12592 ⟨37,by decide⟩).lower ∧ (cell12592 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12592 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12592 ⟨38,by decide⟩).lower ∧ (cell12592 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12592 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12592 ⟨39,by decide⟩).lower ∧ (cell12592 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12592 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12592 ⟨40,by decide⟩).lower ∧ (cell12592 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12592 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12592 ⟨41,by decide⟩).lower ∧ (cell12592 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12592 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12592 ⟨42,by decide⟩).lower ∧ (cell12592 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12592 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12592 ⟨43,by decide⟩).lower ∧ (cell12592 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12592 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12592 ⟨44,by decide⟩).lower ∧ (cell12592 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12592 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12592 ⟨45,by decide⟩).lower ∧ (cell12592 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12592 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12592 ⟨46,by decide⟩).lower ∧ (cell12592 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12592 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12592 ⟨47,by decide⟩).lower ∧ (cell12592 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12592 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12592 ⟨48,by decide⟩).lower ∧ (cell12592 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12592 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12592 ⟨49,by decide⟩).lower ∧ (cell12592 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12592 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12592 ⟨50,by decide⟩).lower ∧ (cell12592 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12592 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12592 ⟨51,by decide⟩).lower ∧ (cell12592 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12592 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12592 ⟨52,by decide⟩).lower ∧ (cell12592 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12592 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12592 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12592 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12592,cell12592,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12592 i).lower ∧
    (cell12592 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12592 i).upper ≤ (0.532 : ℝ) ∧
    (cell12592 i).centre ≤ (0.1 : ℝ) ∧ (cell12592 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12592 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12592 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12592

/-! The local source numeric instances at 12592 have no network premises. -/
namespace BstLean.Part269.N12592
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12592)
open BstLean.Part268 (cell12592)

noncomputable def sourceNumerics12592 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12592 (cell12592 i)
      scalarRow12592.M scalarRow12592.H scalarRow12592.xi := by
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
    energy_allowance := scalarRow12592.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12592]
    centre_nonneg := (scalarRow12592.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12592])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12592
/-! Actual 12593 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12593 ≤ (1.035962371729 : ℝ) := by
  have hr : (112.218536793169 : ℝ) ≤ √(12593 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.218536793169 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12593 12593 (11 / 1000) ≤
    (0.008518085226 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12593) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.218536793169 : ℝ) ≤ √(12593 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12593)
  have hdiv : K / √(12593 : ℝ) ≤ K / 112.218536793169 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.218536793169 ≤ (0.008518085226 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12593.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12593 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12593 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12593 := gPlus_lower 12593
end BstLean.Part269.N12593

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12593
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035962371728 : ℝ) ≤ wn 12593 := by
  have hn : √(12593 : ℝ) ≤ 112.218536793170 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12593 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.218536793170 ≤ 2 / √(12593 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254058605 : ℝ) ≤ rhoBar 12593 BstLean.Part154.csC ∧
    rhoBar 12593 BstLean.Part154.csC ≤ 0.000254058998 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035962371728 : ℝ) / (1.295212 * 12593) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035962371729 : ℝ) / (1.29521 * 12593) := by gcongr
      _ ≤ (0.000254058998 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12593 BstLean.Part154.csC) ≤ 0.001016300538 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12593 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) ≤ 0.000194052055 ∧
    cc1 (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) ≤ 0.000123476595 ∧
    cc2 (rhoBar 12593 BstLean.Part154.csC) ≤ 0.000071679090 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12593 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12593 BstLean.Part154.csC * nuR (rhoBar 12593 BstLean.Part154.csC)) ≤ 0.000508134133 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254058998 : ℝ) * 0.001016300538 := by gcongr
      _ ≤ (0.000508134133 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12593 BstLean.Part154.csC) * nuR (rhoBar 12593 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016300538 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12593 BstLean.Part154.csC) * rhoBar 12593 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254058998 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254058998 / 2 + 0.399 * 0.001016300538 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194052055 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508134133 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123476595 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254058998 / 1.414213562 := by gcongr
      _ ≤ (0.000071679090 : ℝ) := by norm_num

end BstLean.Part269.N12593

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12593
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) ≤ 1.62619E-7 := by
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12593 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12593 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194052055 : ℝ) ^ 2 + 0.000123476595 ^ 2 + 3 * 0.000071679090 ^ 2 +
        2 * 0.797885 * 0.000194052055 * 0.000123476595 + 2 * 0.000194052055 * 0.000071679090 +
        4 * 0.797885 * 0.000123476595 * 0.000071679090 := by gcongr
    _ ≤ (1.62619E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12593 BstLean.Part154.csC Θ ≤ 0.002652414233 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12593 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12593 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035962371729 * 1.62619E-7 / (0.000254058605 : ℝ) := by gcongr
    _ ≤ 0.002652414233 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12593 BstLean.Part154.csC Θ ≤ 0.002943432826 + 0.000670222135 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12593 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035962371729 : ℝ) * ((2 * Θ * 0.000254058998 +
        (6863 / 10000) * 0.000254058998 * 12593 * 0.001016300538) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002943432826 + 0.000670222135 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12593 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12593 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12593 0.011 Θ ∧ gammaRatio 12593 0.011 Θ ≤ 0.000087338914 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12593 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035962371729 : ℝ) * 0.525 / ((1 - 0.011) * 12593) := by gcongr
      _ ≤ (0.000087338914 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12593 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12593 0.011 Θ) :=
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
    badAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12593 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12593 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12593 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12593 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12593 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12593 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12593 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12593 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12593 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12593 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035962371729 : ℝ) * 12593 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003618402348 + 0.003322636368 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12593

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12593
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12593 BstLean.Part154.csC) (piBar (rhoBar 12593 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12593 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12593 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12593 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12593 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12593 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12593 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12593 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12593 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12593 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052709238014 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12593) ≤ 0.010642070510 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12593 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035962371729)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010642070510 + 2 * 0.737676 / 12593) := by gcongr
    _ ≤ (0.052709238014 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12593 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12593

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12593
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498688318 : ℝ) ≤ plow 12593 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12593) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869386442)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392517473) : eMP 12593 0.011 xi bn ≤ 0.001198674992 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12593 : ℝ) * (1 - 0.011))) ≤ 0.000592669448 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392517473 / (12593 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592669448 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592669448 : ℝ) + 3.141593 * 0.052869386442 / (12593 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198674992 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869386442)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392517473) : PiBarMP 12593 12 0.011 xi bn ≤ 0.161941437544 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12593 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037316450435 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.599628135581 : ℝ) ≤ √((12593 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.218536793169 : ℝ) ≤ √(12593 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12593) ≤ 0.124154249921 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037316450435 + 0.052869386442 * 1.772454 / (2 * (111.599628135581 : ℝ))) * (1 + 0.001198674992) +
        8 / (12593 * 112.218536793169) + 0.124154249921 := by gcongr
    _ ≤ (0.161941437544 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869386442)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392517473) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282642677170) :
    parallelOracle 12593 0.011 xi bn cd ≤ 0.162940338621 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12593 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12593 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498688318 : ℝ) ≤ plow 12593 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.218536793169 : ℝ) ≤ √(12593 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282642677170 : ℝ) / (2 * 0.560498688318 * 112.218536793169)) * 0.161941437544 +
        0.282642677170 ^ 2 / (2 * 0.560498688318 * 112.218536793169) := by gcongr
    _ ≤ (0.162940338621 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052869386442) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392517473)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282642677170) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12593 12593 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498688318 : ℝ) ≤ plow 12593 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.218536793169 : ℝ) ≤ √(12593 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12593 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12593 Θ 1.22 ≤ 0.011817125209 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.218536793169 := by gcongr <;> linarith
      _ ≤ (0.011817125209 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12593 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12593 12593 0.011 ≤ 0.008518085226 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12593 12593 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12593 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12593 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12593 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12593 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162940338621 + 0.011817125209 + (0.008518085226 : ℝ) *
        (1 + 2 * (0.282642677170 + 0.011817125209) / (0.560498688318 * 112.218536793169))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12593]

end BstLean.Part269.N12593

/-! The original eight local profiles supply actual 12593 moment certificates. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12593 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052869386442 ∧
    0 ≤ bN 12593 BstLean.Part154.csC (groupTheta g) ∧ bN 12593 BstLean.Part154.csC (groupTheta g) ≤ 0.001392517473 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12593 12593 0.011
      (momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12593 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12593 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12593 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229933439156 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12593 0.011
      (momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12593 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12593
/-! The actual computed-centre upper energy formula at 12593. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12593

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12593)
open BstLean.Part268 (cell12593)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085808736895
  | 2 => 0.086757485970
  | 3 => 0.087705273695
  | 4 => 0.088653723476
  | 5 => 0.089604791831
  | 6 => 0.090560816930
  | 7 => 0.091524571542
  | 8 => 0.092499320392
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12593 12593 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12593 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12593

/-! Actual upper energy certificates on all 43 source endpoints at 12593. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12593)
open BstLean.Part268 (cell12593)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12593 (gMinus 12593) (1 - (cell12593 i).lower) ≤ 1 ∧
    energyUpper 12593 (gMinus 12593) (BstLean.Part211.gPlus 12593)
      (finiteEnergy 12593 12593 0.011) (1 - (cell12593 i).lower) ≤
      (cell12593 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨10,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨11,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨12,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨13,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨14,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨15,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨16,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨17,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨18,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨19,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨20,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨21,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨22,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨23,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨24,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨25,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨26,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨27,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨28,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨29,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨30,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨31,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨32,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨33,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨34,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨35,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨36,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨37,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨38,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨39,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨40,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨41,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨42,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨43,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨44,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨45,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨46,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨47,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨48,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨49,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨50,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨51,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12593) (by norm_num)
        (q := 1 - (cell12593 ⟨52,by decide⟩).lower)
        (by norm_num [cell12593]) (by norm_num [cell12593])
      exact ⟨E.1,E.2.trans (by norm_num [cell12593])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12593

/-! Source-cell containment and simple scalar guards at 12593. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12593)
open BstLean.Part268 (cell12593)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12593 ⟨10,by decide⟩).lower ∧ (cell12593 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12593 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12593 ⟨11,by decide⟩).lower ∧ (cell12593 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12593 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12593 ⟨12,by decide⟩).lower ∧ (cell12593 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12593 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12593 ⟨13,by decide⟩).lower ∧ (cell12593 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12593 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12593 ⟨14,by decide⟩).lower ∧ (cell12593 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12593 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12593 ⟨15,by decide⟩).lower ∧ (cell12593 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12593 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12593 ⟨16,by decide⟩).lower ∧ (cell12593 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12593 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12593 ⟨17,by decide⟩).lower ∧ (cell12593 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12593 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12593 ⟨18,by decide⟩).lower ∧ (cell12593 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12593 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12593 ⟨19,by decide⟩).lower ∧ (cell12593 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12593 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12593 ⟨20,by decide⟩).lower ∧ (cell12593 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12593 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12593 ⟨21,by decide⟩).lower ∧ (cell12593 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12593 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12593 ⟨22,by decide⟩).lower ∧ (cell12593 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12593 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12593 ⟨23,by decide⟩).lower ∧ (cell12593 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12593 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12593 ⟨24,by decide⟩).lower ∧ (cell12593 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12593 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12593 ⟨25,by decide⟩).lower ∧ (cell12593 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12593 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12593 ⟨26,by decide⟩).lower ∧ (cell12593 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12593 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12593 ⟨27,by decide⟩).lower ∧ (cell12593 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12593 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12593 ⟨28,by decide⟩).lower ∧ (cell12593 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12593 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12593 ⟨29,by decide⟩).lower ∧ (cell12593 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12593 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12593 ⟨30,by decide⟩).lower ∧ (cell12593 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12593 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12593 ⟨31,by decide⟩).lower ∧ (cell12593 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12593 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12593 ⟨32,by decide⟩).lower ∧ (cell12593 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12593 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12593 ⟨33,by decide⟩).lower ∧ (cell12593 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12593 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12593 ⟨34,by decide⟩).lower ∧ (cell12593 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12593 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12593 ⟨35,by decide⟩).lower ∧ (cell12593 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12593 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12593 ⟨36,by decide⟩).lower ∧ (cell12593 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12593 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12593 ⟨37,by decide⟩).lower ∧ (cell12593 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12593 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12593 ⟨38,by decide⟩).lower ∧ (cell12593 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12593 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12593 ⟨39,by decide⟩).lower ∧ (cell12593 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12593 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12593 ⟨40,by decide⟩).lower ∧ (cell12593 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12593 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12593 ⟨41,by decide⟩).lower ∧ (cell12593 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12593 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12593 ⟨42,by decide⟩).lower ∧ (cell12593 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12593 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12593 ⟨43,by decide⟩).lower ∧ (cell12593 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12593 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12593 ⟨44,by decide⟩).lower ∧ (cell12593 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12593 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12593 ⟨45,by decide⟩).lower ∧ (cell12593 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12593 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12593 ⟨46,by decide⟩).lower ∧ (cell12593 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12593 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12593 ⟨47,by decide⟩).lower ∧ (cell12593 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12593 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12593 ⟨48,by decide⟩).lower ∧ (cell12593 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12593 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12593 ⟨49,by decide⟩).lower ∧ (cell12593 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12593 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12593 ⟨50,by decide⟩).lower ∧ (cell12593 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12593 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12593 ⟨51,by decide⟩).lower ∧ (cell12593 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12593 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12593 ⟨52,by decide⟩).lower ∧ (cell12593 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12593 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12593 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12593 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12593,cell12593,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12593 i).lower ∧
    (cell12593 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12593 i).upper ≤ (0.532 : ℝ) ∧
    (cell12593 i).centre ≤ (0.1 : ℝ) ∧ (cell12593 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12593 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12593 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12593

/-! The local source numeric instances at 12593 have no network premises. -/
namespace BstLean.Part269.N12593
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12593)
open BstLean.Part268 (cell12593)

noncomputable def sourceNumerics12593 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12593 (cell12593 i)
      scalarRow12593.M scalarRow12593.H scalarRow12593.xi := by
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
    energy_allowance := scalarRow12593.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12593]
    centre_nonneg := (scalarRow12593.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12593])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12593
/-! Actual 12594 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12594 ≤ (1.035960931332 : ℝ) := by
  have hr : (112.222992296587 : ℝ) ≤ √(12594 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.222992296587 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12594 12594 (11 / 1000) ≤
    (0.008517747036 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12594) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.222992296587 : ℝ) ≤ √(12594 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12594)
  have hdiv : K / √(12594 : ℝ) ≤ K / 112.222992296587 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.222992296587 ≤ (0.008517747036 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12594.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12594 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12594 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12594 := gPlus_lower 12594
end BstLean.Part269.N12594

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12594
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035960931331 : ℝ) ≤ wn 12594 := by
  have hn : √(12594 : ℝ) ≤ 112.222992296588 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12594 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.222992296588 ≤ 2 / √(12594 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254038079 : ℝ) ≤ rhoBar 12594 BstLean.Part154.csC ∧
    rhoBar 12594 BstLean.Part154.csC ≤ 0.000254038472 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035960931331 : ℝ) / (1.295212 * 12594) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035960931332 : ℝ) / (1.29521 * 12594) := by gcongr
      _ ≤ (0.000254038472 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12594 BstLean.Part154.csC) ≤ 0.001016218424 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12594 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) ≤ 0.000194036376 ∧
    cc1 (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) ≤ 0.000123466618 ∧
    cc2 (rhoBar 12594 BstLean.Part154.csC) ≤ 0.000071673299 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12594 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12594 BstLean.Part154.csC * nuR (rhoBar 12594 BstLean.Part154.csC)) ≤ 0.000508093078 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254038472 : ℝ) * 0.001016218424 := by gcongr
      _ ≤ (0.000508093078 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12594 BstLean.Part154.csC) * nuR (rhoBar 12594 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016218424 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12594 BstLean.Part154.csC) * rhoBar 12594 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254038472 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254038472 / 2 + 0.399 * 0.001016218424 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194036376 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508093078 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123466618 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254038472 / 1.414213562 := by gcongr
      _ ≤ (0.000071673299 : ℝ) := by norm_num

end BstLean.Part269.N12594

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12594
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) ≤ 1.62593E-7 := by
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12594 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12594 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194036376 : ℝ) ^ 2 + 0.000123466618 ^ 2 + 3 * 0.000071673299 ^ 2 +
        2 * 0.797885 * 0.000194036376 * 0.000123466618 + 2 * 0.000194036376 * 0.000071673299 +
        4 * 0.797885 * 0.000123466618 * 0.000071673299 := by gcongr
    _ ≤ (1.62593E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12594 BstLean.Part154.csC Θ ≤ 0.002652200747 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12594 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12594 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035960931332 * 1.62593E-7 / (0.000254038079 : ℝ) := by gcongr
    _ ≤ 0.002652200747 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12594 BstLean.Part154.csC Θ ≤ 0.002943186824 + 0.000670167055 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12594 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035960931332 : ℝ) * ((2 * Θ * 0.000254038472 +
        (6863 / 10000) * 0.000254038472 * 12594 * 0.001016218424) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002943186824 + 0.000670167055 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12594 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12594 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12594 0.011 Θ ∧ gammaRatio 12594 0.011 Θ ≤ 0.000087331858 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12594 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035960931332 : ℝ) * 0.525 / ((1 - 0.011) * 12594) := by gcongr
      _ ≤ (0.000087331858 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12594 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12594 0.011 Θ) :=
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
    badAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12594 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12594 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12594 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12594 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12594 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12594 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12594 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12594 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12594 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12594 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035960931332 : ℝ) * 12594 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003618156346 + 0.003322367802 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12594

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12594
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12594 BstLean.Part154.csC) (piBar (rhoBar 12594 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12594 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12594 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12594 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12594 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12594 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12594 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12594 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12594 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12594 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052707122553 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12594) ≤ 0.010641647996 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12594 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035960931332)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010641647996 + 2 * 0.737676 / 12594) := by gcongr
    _ ≤ (0.052707122553 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12594 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12594

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12594
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498734309 : ℝ) ≤ plow 12594 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12594) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868999443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392405393) : eMP 12594 0.011 xi bn ≤ 0.001198579073 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12594 : ℝ) * (1 - 0.011))) ≤ 0.000592622067 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392405393 / (12594 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592622067 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592622067 : ℝ) + 3.141593 * 0.052868999443 / (12594 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198579073 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868999443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392405393) : PiBarMP 12594 12 0.011 xi bn ≤ 0.161934980703 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12594 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037314948654 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.604059065967 : ℝ) ≤ √((12594 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.222992296587 : ℝ) ≤ √(12594 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12594) ≤ 0.124149320720 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037314948654 + 0.052868999443 * 1.772454 / (2 * (111.604059065967 : ℝ))) * (1 + 0.001198579073) +
        8 / (12594 * 112.222992296587) + 0.124149320720 := by gcongr
    _ ≤ (0.161934980703 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868999443)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392405393) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282639720162) :
    parallelOracle 12594 0.011 xi bn cd ≤ 0.162933810439 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12594 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12594 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498734309 : ℝ) ≤ plow 12594 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.222992296587 : ℝ) ≤ √(12594 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282639720162 : ℝ) / (2 * 0.560498734309 * 112.222992296587)) * 0.161934980703 +
        0.282639720162 ^ 2 / (2 * 0.560498734309 * 112.222992296587) := by gcongr
    _ ≤ (0.162933810439 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868999443) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392405393)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282639720162) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12594 12594 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498734309 : ℝ) ≤ plow 12594 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.222992296587 : ℝ) ≤ √(12594 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12594 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12594 Θ 1.22 ≤ 0.011816656043 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.222992296587 := by gcongr <;> linarith
      _ ≤ (0.011816656043 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12594 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12594 12594 0.011 ≤ 0.008517747036 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12594 12594 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12594 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12594 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12594 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12594 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162933810439 + 0.011816656043 + (0.008517747036 : ℝ) *
        (1 + 2 * (0.282639720162 + 0.011816656043) / (0.560498734309 * 112.222992296587))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12594]

end BstLean.Part269.N12594

/-! The original eight local profiles supply actual 12594 moment certificates. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12594 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052868999443 ∧
    0 ≤ bN 12594 BstLean.Part154.csC (groupTheta g) ∧ bN 12594 BstLean.Part154.csC (groupTheta g) ≤ 0.001392405393 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12594 12594 0.011
      (momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12594 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12594 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12594 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229932597609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12594 0.011
      (momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12594 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12594
/-! The actual computed-centre upper energy formula at 12594. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12594

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12594)
open BstLean.Part268 (cell12594)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085805698638
  | 2 => 0.086754389053
  | 3 => 0.087702109108
  | 4 => 0.088650480169
  | 5 => 0.089601456357
  | 6 => 0.090557373049
  | 7 => 0.091520999779
  | 8 => 0.092495597546
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12594 12594 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12594 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12594

/-! Actual upper energy certificates on all 43 source endpoints at 12594. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12594)
open BstLean.Part268 (cell12594)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12594 (gMinus 12594) (1 - (cell12594 i).lower) ≤ 1 ∧
    energyUpper 12594 (gMinus 12594) (BstLean.Part211.gPlus 12594)
      (finiteEnergy 12594 12594 0.011) (1 - (cell12594 i).lower) ≤
      (cell12594 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨10,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨11,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨12,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨13,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨14,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨15,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨16,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨17,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨18,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨19,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨20,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨21,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨22,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨23,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨24,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨25,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨26,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨27,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨28,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨29,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨30,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨31,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨32,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨33,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨34,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨35,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨36,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨37,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨38,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨39,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨40,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨41,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨42,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨43,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨44,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨45,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨46,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨47,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨48,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨49,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨50,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨51,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12594) (by norm_num)
        (q := 1 - (cell12594 ⟨52,by decide⟩).lower)
        (by norm_num [cell12594]) (by norm_num [cell12594])
      exact ⟨E.1,E.2.trans (by norm_num [cell12594])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12594

/-! Source-cell containment and simple scalar guards at 12594. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12594)
open BstLean.Part268 (cell12594)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12594 ⟨10,by decide⟩).lower ∧ (cell12594 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12594 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12594 ⟨11,by decide⟩).lower ∧ (cell12594 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12594 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12594 ⟨12,by decide⟩).lower ∧ (cell12594 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12594 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12594 ⟨13,by decide⟩).lower ∧ (cell12594 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12594 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12594 ⟨14,by decide⟩).lower ∧ (cell12594 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12594 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12594 ⟨15,by decide⟩).lower ∧ (cell12594 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12594 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12594 ⟨16,by decide⟩).lower ∧ (cell12594 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12594 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12594 ⟨17,by decide⟩).lower ∧ (cell12594 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12594 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12594 ⟨18,by decide⟩).lower ∧ (cell12594 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12594 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12594 ⟨19,by decide⟩).lower ∧ (cell12594 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12594 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12594 ⟨20,by decide⟩).lower ∧ (cell12594 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12594 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12594 ⟨21,by decide⟩).lower ∧ (cell12594 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12594 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12594 ⟨22,by decide⟩).lower ∧ (cell12594 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12594 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12594 ⟨23,by decide⟩).lower ∧ (cell12594 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12594 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12594 ⟨24,by decide⟩).lower ∧ (cell12594 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12594 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12594 ⟨25,by decide⟩).lower ∧ (cell12594 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12594 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12594 ⟨26,by decide⟩).lower ∧ (cell12594 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12594 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12594 ⟨27,by decide⟩).lower ∧ (cell12594 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12594 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12594 ⟨28,by decide⟩).lower ∧ (cell12594 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12594 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12594 ⟨29,by decide⟩).lower ∧ (cell12594 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12594 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12594 ⟨30,by decide⟩).lower ∧ (cell12594 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12594 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12594 ⟨31,by decide⟩).lower ∧ (cell12594 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12594 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12594 ⟨32,by decide⟩).lower ∧ (cell12594 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12594 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12594 ⟨33,by decide⟩).lower ∧ (cell12594 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12594 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12594 ⟨34,by decide⟩).lower ∧ (cell12594 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12594 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12594 ⟨35,by decide⟩).lower ∧ (cell12594 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12594 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12594 ⟨36,by decide⟩).lower ∧ (cell12594 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12594 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12594 ⟨37,by decide⟩).lower ∧ (cell12594 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12594 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12594 ⟨38,by decide⟩).lower ∧ (cell12594 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12594 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12594 ⟨39,by decide⟩).lower ∧ (cell12594 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12594 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12594 ⟨40,by decide⟩).lower ∧ (cell12594 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12594 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12594 ⟨41,by decide⟩).lower ∧ (cell12594 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12594 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12594 ⟨42,by decide⟩).lower ∧ (cell12594 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12594 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12594 ⟨43,by decide⟩).lower ∧ (cell12594 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12594 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12594 ⟨44,by decide⟩).lower ∧ (cell12594 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12594 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12594 ⟨45,by decide⟩).lower ∧ (cell12594 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12594 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12594 ⟨46,by decide⟩).lower ∧ (cell12594 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12594 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12594 ⟨47,by decide⟩).lower ∧ (cell12594 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12594 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12594 ⟨48,by decide⟩).lower ∧ (cell12594 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12594 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12594 ⟨49,by decide⟩).lower ∧ (cell12594 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12594 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12594 ⟨50,by decide⟩).lower ∧ (cell12594 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12594 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12594 ⟨51,by decide⟩).lower ∧ (cell12594 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12594 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12594 ⟨52,by decide⟩).lower ∧ (cell12594 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12594 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12594 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12594 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12594,cell12594,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12594 i).lower ∧
    (cell12594 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12594 i).upper ≤ (0.532 : ℝ) ∧
    (cell12594 i).centre ≤ (0.1 : ℝ) ∧ (cell12594 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12594 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12594 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12594

/-! The local source numeric instances at 12594 have no network premises. -/
namespace BstLean.Part269.N12594
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12594)
open BstLean.Part268 (cell12594)

noncomputable def sourceNumerics12594 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12594 (cell12594 i)
      scalarRow12594.M scalarRow12594.H scalarRow12594.xi := by
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
    energy_allowance := scalarRow12594.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12594]
    centre_nonneg := (scalarRow12594.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12594])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12594
/-! Actual 12595 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12595 ≤ (1.035959491107 : ℝ) := by
  have hr : (112.227447623119 : ℝ) ≤ √(12595 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.227447623119 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12595 12595 (11 / 1000) ≤
    (0.008517408887 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12595) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.227447623119 : ℝ) ≤ √(12595 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12595)
  have hdiv : K / √(12595 : ℝ) ≤ K / 112.227447623119 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.227447623119 ≤ (0.008517408887 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12595.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12595 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12595 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12595 := gPlus_lower 12595
end BstLean.Part269.N12595

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12595
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035959491106 : ℝ) ≤ wn 12595 := by
  have hn : √(12595 : ℝ) ≤ 112.227447623120 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12595 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.227447623120 ≤ 2 / √(12595 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254017556 : ℝ) ≤ rhoBar 12595 BstLean.Part154.csC ∧
    rhoBar 12595 BstLean.Part154.csC ≤ 0.000254017949 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035959491106 : ℝ) / (1.295212 * 12595) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035959491107 : ℝ) / (1.29521 * 12595) := by gcongr
      _ ≤ (0.000254017949 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12595 BstLean.Part154.csC) ≤ 0.001016136322 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12595 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) ≤ 0.000194020700 ∧
    cc1 (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) ≤ 0.000123456644 ∧
    cc2 (rhoBar 12595 BstLean.Part154.csC) ≤ 0.000071667508 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12595 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12595 BstLean.Part154.csC * nuR (rhoBar 12595 BstLean.Part154.csC)) ≤ 0.000508052030 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254017949 : ℝ) * 0.001016136322 := by gcongr
      _ ≤ (0.000508052030 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12595 BstLean.Part154.csC) * nuR (rhoBar 12595 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016136322 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12595 BstLean.Part154.csC) * rhoBar 12595 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254017949 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254017949 / 2 + 0.399 * 0.001016136322 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194020700 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508052030 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123456644 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254017949 / 1.414213562 := by gcongr
      _ ≤ (0.000071667508 : ℝ) := by norm_num

end BstLean.Part269.N12595

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12595
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) ≤ 1.62567E-7 := by
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12595 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12595 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194020700 : ℝ) ^ 2 + 0.000123456644 ^ 2 + 3 * 0.000071667508 ^ 2 +
        2 * 0.797885 * 0.000194020700 * 0.000123456644 + 2 * 0.000194020700 * 0.000071667508 +
        4 * 0.797885 * 0.000123456644 * 0.000071667508 := by gcongr
    _ ≤ (1.62567E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12595 BstLean.Part154.csC Θ ≤ 0.002651987198 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12595 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12595 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035959491107 * 1.62567E-7 / (0.000254017556 : ℝ) := by gcongr
    _ ≤ 0.002651987198 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12595 BstLean.Part154.csC Θ ≤ 0.002942940855 + 0.000670111982 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12595 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035959491107 : ℝ) * ((2 * Θ * 0.000254017949 +
        (6863 / 10000) * 0.000254017949 * 12595 * 0.001016136322) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002942940855 + 0.000670111982 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12595 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12595 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12595 0.011 Θ ∧ gammaRatio 12595 0.011 Θ ≤ 0.000087324802 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12595 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035959491107 : ℝ) * 0.525 / ((1 - 0.011) * 12595) := by gcongr
      _ ≤ (0.000087324802 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12595 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12595 0.011 Θ) :=
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
    badAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12595 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12595 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12595 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12595 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12595 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12595 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12595 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12595 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12595 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12595 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035959491107 : ℝ) * 12595 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617910377 + 0.003322099180 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12595

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12595
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12595 BstLean.Part154.csC) (piBar (rhoBar 12595 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12595 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12595 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12595 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12595 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12595 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12595 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12595 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12595 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12595 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052705007350 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12595) ≤ 0.010641225533 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12595 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035959491107)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010641225533 + 2 * 0.737676 / 12595) := by gcongr
    _ ≤ (0.052705007350 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12595 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12595

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12595
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498780293 : ℝ) ≤ plow 12595 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12595) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868612447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392293279) : eMP 12595 0.011 xi bn ≤ 0.001198483147 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12595 : ℝ) * (1 - 0.011))) ≤ 0.000592574682 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392293279 / (12595 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592574682 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592574682 : ℝ) + 3.141593 * 0.052868612447 / (12595 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198483147 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868612447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392293279) : PiBarMP 12595 12 0.011 xi bn ≤ 0.161928523934 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12595 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037313446357 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.608489820443 : ℝ) ≤ √((12595 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.227447623119 : ℝ) ≤ √(12595 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12595) ≤ 0.124144392106 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037313446357 + 0.052868612447 * 1.772454 / (2 * (111.608489820443 : ℝ))) * (1 + 0.001198483147) +
        8 / (12595 * 112.227447623119) + 0.124144392106 := by gcongr
    _ ≤ (0.161928523934 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868612447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392293279) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282636763415) :
    parallelOracle 12595 0.011 xi bn cd ≤ 0.162927282339 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12595 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12595 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498780293 : ℝ) ≤ plow 12595 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.227447623119 : ℝ) ≤ √(12595 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282636763415 : ℝ) / (2 * 0.560498780293 * 112.227447623119)) * 0.161928523934 +
        0.282636763415 ^ 2 / (2 * 0.560498780293 * 112.227447623119) := by gcongr
    _ ≤ (0.162927282339 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868612447) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392293279)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282636763415) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12595 12595 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498780293 : ℝ) ≤ plow 12595 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.227447623119 : ℝ) ≤ √(12595 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12595 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12595 Θ 1.22 ≤ 0.011816186932 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.227447623119 := by gcongr <;> linarith
      _ ≤ (0.011816186932 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12595 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12595 12595 0.011 ≤ 0.008517408887 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12595 12595 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12595 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12595 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12595 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12595 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162927282339 + 0.011816186932 + (0.008517408887 : ℝ) *
        (1 + 2 * (0.282636763415 + 0.011816186932) / (0.560498780293 * 112.227447623119))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12595]

end BstLean.Part269.N12595

/-! The original eight local profiles supply actual 12595 moment certificates. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12595 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052868612447 ∧
    0 ≤ bN 12595 BstLean.Part154.csC (groupTheta g) ∧ bN 12595 BstLean.Part154.csC (groupTheta g) ≤ 0.001392293279 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12595 12595 0.011
      (momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12595 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12595 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12595 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229931756065 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12595 0.011
      (momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12595 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12595
/-! The actual computed-centre upper energy formula at 12595. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12595

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12595)
open BstLean.Part268 (cell12595)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085802661590
  | 2 => 0.086751293396
  | 3 => 0.087698945844
  | 4 => 0.088647238262
  | 5 => 0.089598122378
  | 6 => 0.090553930778
  | 7 => 0.091517429765
  | 8 => 0.092491876614
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12595 12595 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12595 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12595

/-! Actual upper energy certificates on all 43 source endpoints at 12595. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12595)
open BstLean.Part268 (cell12595)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12595 (gMinus 12595) (1 - (cell12595 i).lower) ≤ 1 ∧
    energyUpper 12595 (gMinus 12595) (BstLean.Part211.gPlus 12595)
      (finiteEnergy 12595 12595 0.011) (1 - (cell12595 i).lower) ≤
      (cell12595 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨10,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨11,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨12,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨13,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨14,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨15,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨16,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨17,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨18,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨19,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨20,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨21,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨22,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨23,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨24,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨25,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨26,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨27,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨28,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨29,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨30,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨31,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨32,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨33,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨34,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨35,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨36,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨37,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨38,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨39,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨40,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨41,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨42,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨43,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨44,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨45,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨46,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨47,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨48,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨49,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨50,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨51,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12595) (by norm_num)
        (q := 1 - (cell12595 ⟨52,by decide⟩).lower)
        (by norm_num [cell12595]) (by norm_num [cell12595])
      exact ⟨E.1,E.2.trans (by norm_num [cell12595])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12595

/-! Source-cell containment and simple scalar guards at 12595. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12595)
open BstLean.Part268 (cell12595)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12595 ⟨10,by decide⟩).lower ∧ (cell12595 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12595 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12595 ⟨11,by decide⟩).lower ∧ (cell12595 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12595 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12595 ⟨12,by decide⟩).lower ∧ (cell12595 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12595 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12595 ⟨13,by decide⟩).lower ∧ (cell12595 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12595 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12595 ⟨14,by decide⟩).lower ∧ (cell12595 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12595 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12595 ⟨15,by decide⟩).lower ∧ (cell12595 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12595 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12595 ⟨16,by decide⟩).lower ∧ (cell12595 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12595 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12595 ⟨17,by decide⟩).lower ∧ (cell12595 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12595 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12595 ⟨18,by decide⟩).lower ∧ (cell12595 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12595 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12595 ⟨19,by decide⟩).lower ∧ (cell12595 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12595 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12595 ⟨20,by decide⟩).lower ∧ (cell12595 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12595 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12595 ⟨21,by decide⟩).lower ∧ (cell12595 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12595 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12595 ⟨22,by decide⟩).lower ∧ (cell12595 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12595 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12595 ⟨23,by decide⟩).lower ∧ (cell12595 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12595 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12595 ⟨24,by decide⟩).lower ∧ (cell12595 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12595 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12595 ⟨25,by decide⟩).lower ∧ (cell12595 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12595 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12595 ⟨26,by decide⟩).lower ∧ (cell12595 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12595 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12595 ⟨27,by decide⟩).lower ∧ (cell12595 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12595 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12595 ⟨28,by decide⟩).lower ∧ (cell12595 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12595 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12595 ⟨29,by decide⟩).lower ∧ (cell12595 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12595 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12595 ⟨30,by decide⟩).lower ∧ (cell12595 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12595 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12595 ⟨31,by decide⟩).lower ∧ (cell12595 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12595 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12595 ⟨32,by decide⟩).lower ∧ (cell12595 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12595 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12595 ⟨33,by decide⟩).lower ∧ (cell12595 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12595 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12595 ⟨34,by decide⟩).lower ∧ (cell12595 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12595 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12595 ⟨35,by decide⟩).lower ∧ (cell12595 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12595 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12595 ⟨36,by decide⟩).lower ∧ (cell12595 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12595 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12595 ⟨37,by decide⟩).lower ∧ (cell12595 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12595 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12595 ⟨38,by decide⟩).lower ∧ (cell12595 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12595 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12595 ⟨39,by decide⟩).lower ∧ (cell12595 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12595 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12595 ⟨40,by decide⟩).lower ∧ (cell12595 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12595 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12595 ⟨41,by decide⟩).lower ∧ (cell12595 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12595 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12595 ⟨42,by decide⟩).lower ∧ (cell12595 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12595 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12595 ⟨43,by decide⟩).lower ∧ (cell12595 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12595 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12595 ⟨44,by decide⟩).lower ∧ (cell12595 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12595 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12595 ⟨45,by decide⟩).lower ∧ (cell12595 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12595 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12595 ⟨46,by decide⟩).lower ∧ (cell12595 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12595 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12595 ⟨47,by decide⟩).lower ∧ (cell12595 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12595 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12595 ⟨48,by decide⟩).lower ∧ (cell12595 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12595 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12595 ⟨49,by decide⟩).lower ∧ (cell12595 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12595 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12595 ⟨50,by decide⟩).lower ∧ (cell12595 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12595 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12595 ⟨51,by decide⟩).lower ∧ (cell12595 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12595 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12595 ⟨52,by decide⟩).lower ∧ (cell12595 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12595 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12595 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12595 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12595,cell12595,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12595 i).lower ∧
    (cell12595 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12595 i).upper ≤ (0.532 : ℝ) ∧
    (cell12595 i).centre ≤ (0.1 : ℝ) ∧ (cell12595 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12595 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12595 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12595

/-! The local source numeric instances at 12595 have no network premises. -/
namespace BstLean.Part269.N12595
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12595)
open BstLean.Part268 (cell12595)

noncomputable def sourceNumerics12595 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12595 (cell12595 i)
      scalarRow12595.M scalarRow12595.H scalarRow12595.xi := by
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
    energy_allowance := scalarRow12595.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12595]
    centre_nonneg := (scalarRow12595.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12595])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12595
/-! Actual 12596 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12596 ≤ (1.035958051056 : ℝ) := by
  have hr : (112.231902772785 : ℝ) ≤ √(12596 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.231902772785 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12596 12596 (11 / 1000) ≤
    (0.008517070778 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12596) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.231902772785 : ℝ) ≤ √(12596 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12596)
  have hdiv : K / √(12596 : ℝ) ≤ K / 112.231902772785 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.231902772785 ≤ (0.008517070778 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12596.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12596 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12596 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12596 := gPlus_lower 12596
end BstLean.Part269.N12596

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12596
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035958051055 : ℝ) ≤ wn 12596 := by
  have hn : √(12596 : ℝ) ≤ 112.231902772786 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12596 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.231902772786 ≤ 2 / √(12596 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253997036 : ℝ) ≤ rhoBar 12596 BstLean.Part154.csC ∧
    rhoBar 12596 BstLean.Part154.csC ≤ 0.000253997429 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035958051055 : ℝ) / (1.295212 * 12596) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035958051056 : ℝ) / (1.29521 * 12596) := by gcongr
      _ ≤ (0.000253997429 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12596 BstLean.Part154.csC) ≤ 0.001016054231 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12596 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) ≤ 0.000194005026 ∧
    cc1 (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) ≤ 0.000123446670 ∧
    cc2 (rhoBar 12596 BstLean.Part154.csC) ≤ 0.000071661719 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12596 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12596 BstLean.Part154.csC * nuR (rhoBar 12596 BstLean.Part154.csC)) ≤ 0.000508010987 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253997429 : ℝ) * 0.001016054231 := by gcongr
      _ ≤ (0.000508010987 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12596 BstLean.Part154.csC) * nuR (rhoBar 12596 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016054231 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12596 BstLean.Part154.csC) * rhoBar 12596 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253997429 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253997429 / 2 + 0.399 * 0.001016054231 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194005026 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508010987 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123446670 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253997429 / 1.414213562 := by gcongr
      _ ≤ (0.000071661719 : ℝ) := by norm_num

end BstLean.Part269.N12596

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12596
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) ≤ 1.62540E-7 := by
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12596 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12596 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194005026 : ℝ) ^ 2 + 0.000123446670 ^ 2 + 3 * 0.000071661719 ^ 2 +
        2 * 0.797885 * 0.000194005026 * 0.000123446670 + 2 * 0.000194005026 * 0.000071661719 +
        4 * 0.797885 * 0.000123446670 * 0.000071661719 := by gcongr
    _ ≤ (1.62540E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12596 BstLean.Part154.csC Θ ≤ 0.002651757269 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12596 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12596 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035958051056 * 1.62540E-7 / (0.000253997036 : ℝ) := by gcongr
    _ ≤ 0.002651757269 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12596 BstLean.Part154.csC Θ ≤ 0.002942694917 + 0.000670056918 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12596 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035958051056 : ℝ) * ((2 * Θ * 0.000253997429 +
        (6863 / 10000) * 0.000253997429 * 12596 * 0.001016054231) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002942694917 + 0.000670056918 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12596 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12596 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12596 0.011 Θ ∧ gammaRatio 12596 0.011 Θ ≤ 0.000087317748 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12596 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035958051056 : ℝ) * 0.525 / ((1 - 0.011) * 12596) := by gcongr
      _ ≤ (0.000087317748 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12596 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12596 0.011 Θ) :=
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
    badAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12596 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12596 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12596 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12596 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12596 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12596 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12596 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12596 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12596 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12596 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035958051056 : ℝ) * 12596 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617664439 + 0.003321814187 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12596

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12596
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12596 BstLean.Part154.csC) (piBar (rhoBar 12596 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12596 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12596 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12596 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12596 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12596 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12596 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12596 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12596 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12596 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052702892393 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12596) ≤ 0.010640803119 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12596 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035958051056)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010640803119 + 2 * 0.737676 / 12596) := by gcongr
    _ ≤ (0.052702892393 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12596 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12596

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12596
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498826270 : ℝ) ≤ plow 12596 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12596) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868216888)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392172567) : eMP 12596 0.011 xi bn ≤ 0.001198383569 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12596 : ℝ) * (1 - 0.011))) ≤ 0.000592525472 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392172567 / (12596 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592525472 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592525472 : ℝ) + 3.141593 * 0.052868216888 / (12596 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198383569 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868216888)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392172567) : PiBarMP 12596 12 0.011 xi bn ≤ 0.161921952133 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12596 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037311828782 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.612920399029 : ℝ) ≤ √((12596 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.231902772785 : ℝ) ≤ √(12596 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12596) ≤ 0.124139464079 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037311828782 + 0.052868216888 * 1.772454 / (2 * (111.612920399029 : ℝ))) * (1 + 0.001198383569) +
        8 / (12596 * 112.231902772785) + 0.124139464079 := by gcongr
    _ ≤ (0.161921952133 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868216888)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392172567) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282633788291) :
    parallelOracle 12596 0.011 xi bn cd ≤ 0.162920638849 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12596 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12596 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498826270 : ℝ) ≤ plow 12596 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.231902772785 : ℝ) ≤ √(12596 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282633788291 : ℝ) / (2 * 0.560498826270 * 112.231902772785)) * 0.161921952133 +
        0.282633788291 ^ 2 / (2 * 0.560498826270 * 112.231902772785) := by gcongr
    _ ≤ (0.162920638849 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052868216888) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392172567)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282633788291) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12596 12596 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498826270 : ℝ) ≤ plow 12596 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.231902772785 : ℝ) ≤ √(12596 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12596 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12596 Θ 1.22 ≤ 0.011815717878 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.231902772785 := by gcongr <;> linarith
      _ ≤ (0.011815717878 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12596 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12596 12596 0.011 ≤ 0.008517070778 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12596 12596 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12596 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12596 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12596 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12596 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162920638849 + 0.011815717878 + (0.008517070778 : ℝ) *
        (1 + 2 * (0.282633788291 + 0.011815717878) / (0.560498826270 * 112.231902772785))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12596]

end BstLean.Part269.N12596

/-! The original eight local profiles supply actual 12596 moment certificates. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12596 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052868216888 ∧
    0 ≤ bN 12596 BstLean.Part154.csC (groupTheta g) ∧ bN 12596 BstLean.Part154.csC (groupTheta g) ≤ 0.001392172567 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12596 12596 0.011
      (momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12596 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12596 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12596 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229930895898 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12596 0.011
      (momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12596 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12596
/-! The actual computed-centre upper energy formula at 12596. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12596

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12596)
open BstLean.Part268 (cell12596)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085799625749
  | 2 => 0.086748198997
  | 3 => 0.087695783901
  | 4 => 0.088643997754
  | 5 => 0.089594789892
  | 6 => 0.090550490115
  | 7 => 0.091513861496
  | 8 => 0.092488157595
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12596 12596 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12596 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12596

/-! Actual upper energy certificates on all 43 source endpoints at 12596. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12596)
open BstLean.Part268 (cell12596)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12596 (gMinus 12596) (1 - (cell12596 i).lower) ≤ 1 ∧
    energyUpper 12596 (gMinus 12596) (BstLean.Part211.gPlus 12596)
      (finiteEnergy 12596 12596 0.011) (1 - (cell12596 i).lower) ≤
      (cell12596 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨10,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨11,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨12,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨13,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨14,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨15,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨16,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨17,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨18,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨19,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨20,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨21,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨22,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨23,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨24,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨25,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨26,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨27,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨28,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨29,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨30,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨31,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨32,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨33,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨34,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨35,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨36,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨37,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨38,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨39,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨40,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨41,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨42,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨43,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨44,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨45,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨46,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨47,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨48,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨49,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨50,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨51,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12596) (by norm_num)
        (q := 1 - (cell12596 ⟨52,by decide⟩).lower)
        (by norm_num [cell12596]) (by norm_num [cell12596])
      exact ⟨E.1,E.2.trans (by norm_num [cell12596])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12596

/-! Source-cell containment and simple scalar guards at 12596. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12596)
open BstLean.Part268 (cell12596)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12596 ⟨10,by decide⟩).lower ∧ (cell12596 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12596 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12596 ⟨11,by decide⟩).lower ∧ (cell12596 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12596 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12596 ⟨12,by decide⟩).lower ∧ (cell12596 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12596 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12596 ⟨13,by decide⟩).lower ∧ (cell12596 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12596 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12596 ⟨14,by decide⟩).lower ∧ (cell12596 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12596 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12596 ⟨15,by decide⟩).lower ∧ (cell12596 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12596 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12596 ⟨16,by decide⟩).lower ∧ (cell12596 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12596 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12596 ⟨17,by decide⟩).lower ∧ (cell12596 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12596 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12596 ⟨18,by decide⟩).lower ∧ (cell12596 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12596 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12596 ⟨19,by decide⟩).lower ∧ (cell12596 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12596 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12596 ⟨20,by decide⟩).lower ∧ (cell12596 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12596 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12596 ⟨21,by decide⟩).lower ∧ (cell12596 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12596 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12596 ⟨22,by decide⟩).lower ∧ (cell12596 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12596 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12596 ⟨23,by decide⟩).lower ∧ (cell12596 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12596 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12596 ⟨24,by decide⟩).lower ∧ (cell12596 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12596 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12596 ⟨25,by decide⟩).lower ∧ (cell12596 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12596 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12596 ⟨26,by decide⟩).lower ∧ (cell12596 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12596 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12596 ⟨27,by decide⟩).lower ∧ (cell12596 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12596 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12596 ⟨28,by decide⟩).lower ∧ (cell12596 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12596 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12596 ⟨29,by decide⟩).lower ∧ (cell12596 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12596 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12596 ⟨30,by decide⟩).lower ∧ (cell12596 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12596 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12596 ⟨31,by decide⟩).lower ∧ (cell12596 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12596 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12596 ⟨32,by decide⟩).lower ∧ (cell12596 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12596 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12596 ⟨33,by decide⟩).lower ∧ (cell12596 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12596 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12596 ⟨34,by decide⟩).lower ∧ (cell12596 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12596 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12596 ⟨35,by decide⟩).lower ∧ (cell12596 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12596 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12596 ⟨36,by decide⟩).lower ∧ (cell12596 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12596 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12596 ⟨37,by decide⟩).lower ∧ (cell12596 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12596 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12596 ⟨38,by decide⟩).lower ∧ (cell12596 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12596 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12596 ⟨39,by decide⟩).lower ∧ (cell12596 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12596 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12596 ⟨40,by decide⟩).lower ∧ (cell12596 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12596 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12596 ⟨41,by decide⟩).lower ∧ (cell12596 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12596 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12596 ⟨42,by decide⟩).lower ∧ (cell12596 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12596 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12596 ⟨43,by decide⟩).lower ∧ (cell12596 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12596 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12596 ⟨44,by decide⟩).lower ∧ (cell12596 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12596 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12596 ⟨45,by decide⟩).lower ∧ (cell12596 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12596 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12596 ⟨46,by decide⟩).lower ∧ (cell12596 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12596 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12596 ⟨47,by decide⟩).lower ∧ (cell12596 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12596 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12596 ⟨48,by decide⟩).lower ∧ (cell12596 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12596 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12596 ⟨49,by decide⟩).lower ∧ (cell12596 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12596 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12596 ⟨50,by decide⟩).lower ∧ (cell12596 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12596 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12596 ⟨51,by decide⟩).lower ∧ (cell12596 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12596 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12596 ⟨52,by decide⟩).lower ∧ (cell12596 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12596 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12596 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12596 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12596,cell12596,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12596 i).lower ∧
    (cell12596 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12596 i).upper ≤ (0.532 : ℝ) ∧
    (cell12596 i).centre ≤ (0.1 : ℝ) ∧ (cell12596 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12596 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12596 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12596

/-! The local source numeric instances at 12596 have no network premises. -/
namespace BstLean.Part269.N12596
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12596)
open BstLean.Part268 (cell12596)

noncomputable def sourceNumerics12596 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12596 (cell12596 i)
      scalarRow12596.M scalarRow12596.H scalarRow12596.xi := by
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
    energy_allowance := scalarRow12596.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12596]
    centre_nonneg := (scalarRow12596.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12596])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12596
/-! Actual 12597 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12597 ≤ (1.035956611176 : ℝ) := by
  have hr : (112.236357745607 : ℝ) ≤ √(12597 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.236357745607 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12597 12597 (11 / 1000) ≤
    (0.008516732709 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12597) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.236357745607 : ℝ) ≤ √(12597 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12597)
  have hdiv : K / √(12597 : ℝ) ≤ K / 112.236357745607 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.236357745607 ≤ (0.008516732709 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12597.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12597 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12597 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12597 := gPlus_lower 12597
end BstLean.Part269.N12597

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12597
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035956611175 : ℝ) ≤ wn 12597 := by
  have hn : √(12597 : ℝ) ≤ 112.236357745608 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12597 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.236357745608 ≤ 2 / √(12597 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253976520 : ℝ) ≤ rhoBar 12597 BstLean.Part154.csC ∧
    rhoBar 12597 BstLean.Part154.csC ≤ 0.000253976913 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035956611175 : ℝ) / (1.295212 * 12597) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035956611176 : ℝ) / (1.29521 * 12597) := by gcongr
      _ ≤ (0.000253976913 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12597 BstLean.Part154.csC) ≤ 0.001015972157 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12597 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) ≤ 0.000193989355 ∧
    cc1 (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) ≤ 0.000123436699 ∧
    cc2 (rhoBar 12597 BstLean.Part154.csC) ≤ 0.000071655931 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12597 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12597 BstLean.Part154.csC * nuR (rhoBar 12597 BstLean.Part154.csC)) ≤ 0.000507969952 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253976913 : ℝ) * 0.001015972157 := by gcongr
      _ ≤ (0.000507969952 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12597 BstLean.Part154.csC) * nuR (rhoBar 12597 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015972157 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12597 BstLean.Part154.csC) * rhoBar 12597 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253976913 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253976913 / 2 + 0.399 * 0.001015972157 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193989355 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507969952 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123436699 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253976913 / 1.414213562 := by gcongr
      _ ≤ (0.000071655931 : ℝ) := by norm_num

end BstLean.Part269.N12597

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12597
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) ≤ 1.62514E-7 := by
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12597 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12597 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193989355 : ℝ) ^ 2 + 0.000123436699 ^ 2 + 3 * 0.000071655931 ^ 2 +
        2 * 0.797885 * 0.000193989355 * 0.000123436699 + 2 * 0.000193989355 * 0.000071655931 +
        4 * 0.797885 * 0.000123436699 * 0.000071655931 := by gcongr
    _ ≤ (1.62514E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12597 BstLean.Part154.csC Θ ≤ 0.002651543580 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12597 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12597 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035956611176 * 1.62514E-7 / (0.000253976520 : ℝ) := by gcongr
    _ ≤ 0.002651543580 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12597 BstLean.Part154.csC Θ ≤ 0.002942449039 + 0.000670001865 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12597 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035956611176 : ℝ) * ((2 * Θ * 0.000253976913 +
        (6863 / 10000) * 0.000253976913 * 12597 * 0.001015972157) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002942449039 + 0.000670001865 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12597 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12597 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12597 0.011 Θ ∧ gammaRatio 12597 0.011 Θ ≤ 0.000087310695 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12597 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035956611176 : ℝ) * 0.525 / ((1 - 0.011) * 12597) := by gcongr
      _ ≤ (0.000087310695 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12597 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12597 0.011 Θ) :=
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
    badAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12597 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12597 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12597 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12597 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12597 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12597 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12597 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12597 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12597 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12597 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035956611176 : ℝ) * 12597 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617418561 + 0.003321545445 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12597

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12597
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12597 BstLean.Part154.csC) (piBar (rhoBar 12597 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12597 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12597 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12597 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12597 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12597 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12597 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12597 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12597 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12597 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052700777694 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12597) ≤ 0.010640380756 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12597 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035956611176)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010640380756 + 2 * 0.737676 / 12597) := by gcongr
    _ ≤ (0.052700777694 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12597 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12597

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12597
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498872239 : ℝ) ≤ plow 12597 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12597) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867829920)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392060380) : eMP 12597 0.011 xi bn ≤ 0.001198287627 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12597 : ℝ) * (1 - 0.011))) ≤ 0.000592478079 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001392060380 / (12597 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592478079 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592478079 : ℝ) + 3.141593 * 0.052867829920 / (12597 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198287627 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867829920)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392060380) : PiBarMP 12597 12 0.011 xi bn ≤ 0.161915495438 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12597 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037310325381 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.617350801745 : ℝ) ≤ √((12597 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.236357745607 : ℝ) ≤ √(12597 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12597) ≤ 0.124134536639 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037310325381 + 0.052867829920 * 1.772454 / (2 * (111.617350801745 : ℝ))) * (1 + 0.001198287627) +
        8 / (12597 * 112.236357745607) + 0.124134536639 := by gcongr
    _ ≤ (0.161915495438 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867829920)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392060380) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282630832102) :
    parallelOracle 12597 0.011 xi bn cd ≤ 0.162914110842 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12597 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12597 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498872239 : ℝ) ≤ plow 12597 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.236357745607 : ℝ) ≤ √(12597 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282630832102 : ℝ) / (2 * 0.560498872239 * 112.236357745607)) * 0.161915495438 +
        0.282630832102 ^ 2 / (2 * 0.560498872239 * 112.236357745607) := by gcongr
    _ ≤ (0.162914110842 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867829920) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001392060380)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282630832102) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12597 12597 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498872239 : ℝ) ≤ plow 12597 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.236357745607 : ℝ) ≤ √(12597 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12597 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12597 Θ 1.22 ≤ 0.011815248879 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.236357745607 := by gcongr <;> linarith
      _ ≤ (0.011815248879 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12597 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12597 12597 0.011 ≤ 0.008516732709 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12597 12597 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12597 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12597 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12597 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12597 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162914110842 + 0.011815248879 + (0.008516732709 : ℝ) *
        (1 + 2 * (0.282630832102 + 0.011815248879) / (0.560498872239 * 112.236357745607))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12597]

end BstLean.Part269.N12597

/-! The original eight local profiles supply actual 12597 moment certificates. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12597 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867829920 ∧
    0 ≤ bN 12597 BstLean.Part154.csC (groupTheta g) ∧ bN 12597 BstLean.Part154.csC (groupTheta g) ≤ 0.001392060380 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12597 12597 0.011
      (momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12597 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12597 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12597 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229930054408 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12597 0.011
      (momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12597 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12597
/-! The actual computed-centre upper energy formula at 12597. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12597

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12597)
open BstLean.Part268 (cell12597)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085796591115
  | 2 => 0.086745105855
  | 3 => 0.087692623279
  | 4 => 0.088640758643
  | 5 => 0.089591458897
  | 6 => 0.090547051058
  | 7 => 0.091510294972
  | 8 => 0.092484440486
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12597 12597 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12597 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12597

/-! Actual upper energy certificates on all 43 source endpoints at 12597. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12597)
open BstLean.Part268 (cell12597)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12597 (gMinus 12597) (1 - (cell12597 i).lower) ≤ 1 ∧
    energyUpper 12597 (gMinus 12597) (BstLean.Part211.gPlus 12597)
      (finiteEnergy 12597 12597 0.011) (1 - (cell12597 i).lower) ≤
      (cell12597 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨10,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨11,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨12,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨13,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨14,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨15,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨16,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨17,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨18,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨19,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨20,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨21,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨22,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨23,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨24,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨25,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨26,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨27,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨28,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨29,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨30,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨31,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨32,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨33,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨34,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨35,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨36,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨37,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨38,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨39,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨40,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨41,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨42,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨43,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨44,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨45,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨46,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨47,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨48,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨49,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨50,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨51,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12597) (by norm_num)
        (q := 1 - (cell12597 ⟨52,by decide⟩).lower)
        (by norm_num [cell12597]) (by norm_num [cell12597])
      exact ⟨E.1,E.2.trans (by norm_num [cell12597])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12597

/-! Source-cell containment and simple scalar guards at 12597. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12597)
open BstLean.Part268 (cell12597)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12597 ⟨10,by decide⟩).lower ∧ (cell12597 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12597 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12597 ⟨11,by decide⟩).lower ∧ (cell12597 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12597 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12597 ⟨12,by decide⟩).lower ∧ (cell12597 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12597 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12597 ⟨13,by decide⟩).lower ∧ (cell12597 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12597 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12597 ⟨14,by decide⟩).lower ∧ (cell12597 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12597 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12597 ⟨15,by decide⟩).lower ∧ (cell12597 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12597 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12597 ⟨16,by decide⟩).lower ∧ (cell12597 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12597 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12597 ⟨17,by decide⟩).lower ∧ (cell12597 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12597 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12597 ⟨18,by decide⟩).lower ∧ (cell12597 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12597 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12597 ⟨19,by decide⟩).lower ∧ (cell12597 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12597 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12597 ⟨20,by decide⟩).lower ∧ (cell12597 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12597 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12597 ⟨21,by decide⟩).lower ∧ (cell12597 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12597 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12597 ⟨22,by decide⟩).lower ∧ (cell12597 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12597 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12597 ⟨23,by decide⟩).lower ∧ (cell12597 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12597 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12597 ⟨24,by decide⟩).lower ∧ (cell12597 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12597 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12597 ⟨25,by decide⟩).lower ∧ (cell12597 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12597 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12597 ⟨26,by decide⟩).lower ∧ (cell12597 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12597 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12597 ⟨27,by decide⟩).lower ∧ (cell12597 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12597 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12597 ⟨28,by decide⟩).lower ∧ (cell12597 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12597 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12597 ⟨29,by decide⟩).lower ∧ (cell12597 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12597 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12597 ⟨30,by decide⟩).lower ∧ (cell12597 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12597 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12597 ⟨31,by decide⟩).lower ∧ (cell12597 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12597 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12597 ⟨32,by decide⟩).lower ∧ (cell12597 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12597 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12597 ⟨33,by decide⟩).lower ∧ (cell12597 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12597 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12597 ⟨34,by decide⟩).lower ∧ (cell12597 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12597 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12597 ⟨35,by decide⟩).lower ∧ (cell12597 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12597 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12597 ⟨36,by decide⟩).lower ∧ (cell12597 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12597 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12597 ⟨37,by decide⟩).lower ∧ (cell12597 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12597 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12597 ⟨38,by decide⟩).lower ∧ (cell12597 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12597 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12597 ⟨39,by decide⟩).lower ∧ (cell12597 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12597 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12597 ⟨40,by decide⟩).lower ∧ (cell12597 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12597 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12597 ⟨41,by decide⟩).lower ∧ (cell12597 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12597 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12597 ⟨42,by decide⟩).lower ∧ (cell12597 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12597 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12597 ⟨43,by decide⟩).lower ∧ (cell12597 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12597 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12597 ⟨44,by decide⟩).lower ∧ (cell12597 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12597 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12597 ⟨45,by decide⟩).lower ∧ (cell12597 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12597 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12597 ⟨46,by decide⟩).lower ∧ (cell12597 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12597 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12597 ⟨47,by decide⟩).lower ∧ (cell12597 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12597 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12597 ⟨48,by decide⟩).lower ∧ (cell12597 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12597 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12597 ⟨49,by decide⟩).lower ∧ (cell12597 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12597 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12597 ⟨50,by decide⟩).lower ∧ (cell12597 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12597 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12597 ⟨51,by decide⟩).lower ∧ (cell12597 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12597 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12597 ⟨52,by decide⟩).lower ∧ (cell12597 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12597 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12597 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12597 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12597,cell12597,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12597 i).lower ∧
    (cell12597 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12597 i).upper ≤ (0.532 : ℝ) ∧
    (cell12597 i).centre ≤ (0.1 : ℝ) ∧ (cell12597 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12597 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12597 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12597

/-! The local source numeric instances at 12597 have no network premises. -/
namespace BstLean.Part269.N12597
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12597)
open BstLean.Part268 (cell12597)

noncomputable def sourceNumerics12597 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12597 (cell12597 i)
      scalarRow12597.M scalarRow12597.H scalarRow12597.xi := by
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
    energy_allowance := scalarRow12597.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12597]
    centre_nonneg := (scalarRow12597.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12597])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12597
/-! Actual 12598 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12598 ≤ (1.035955171469 : ℝ) := by
  have hr : (112.240812541606 : ℝ) ≤ √(12598 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.240812541606 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12598 12598 (11 / 1000) ≤
    (0.008516394681 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12598) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.240812541606 : ℝ) ≤ √(12598 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12598)
  have hdiv : K / √(12598 : ℝ) ≤ K / 112.240812541606 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.240812541606 ≤ (0.008516394681 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12598.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12598 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12598 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12598 := gPlus_lower 12598
end BstLean.Part269.N12598

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12598
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035955171468 : ℝ) ≤ wn 12598 := by
  have hn : √(12598 : ℝ) ≤ 112.240812541607 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12598 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.240812541607 ≤ 2 / √(12598 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253956007 : ℝ) ≤ rhoBar 12598 BstLean.Part154.csC ∧
    rhoBar 12598 BstLean.Part154.csC ≤ 0.000253956400 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035955171468 : ℝ) / (1.295212 * 12598) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035955171469 : ℝ) / (1.29521 * 12598) := by gcongr
      _ ≤ (0.000253956400 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12598 BstLean.Part154.csC) ≤ 0.001015890094 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12598 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) ≤ 0.000193973686 ∧
    cc1 (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) ≤ 0.000123426729 ∧
    cc2 (rhoBar 12598 BstLean.Part154.csC) ≤ 0.000071650143 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12598 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12598 BstLean.Part154.csC * nuR (rhoBar 12598 BstLean.Part154.csC)) ≤ 0.000507928924 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253956400 : ℝ) * 0.001015890094 := by gcongr
      _ ≤ (0.000507928924 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12598 BstLean.Part154.csC) * nuR (rhoBar 12598 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015890094 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12598 BstLean.Part154.csC) * rhoBar 12598 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253956400 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253956400 / 2 + 0.399 * 0.001015890094 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193973686 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507928924 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123426729 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253956400 / 1.414213562 := by gcongr
      _ ≤ (0.000071650143 : ℝ) := by norm_num

end BstLean.Part269.N12598

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12598
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) ≤ 1.62488E-7 := by
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12598 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12598 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193973686 : ℝ) ^ 2 + 0.000123426729 ^ 2 + 3 * 0.000071650143 ^ 2 +
        2 * 0.797885 * 0.000193973686 * 0.000123426729 + 2 * 0.000193973686 * 0.000071650143 +
        4 * 0.797885 * 0.000123426729 * 0.000071650143 := by gcongr
    _ ≤ (1.62488E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12598 BstLean.Part154.csC Θ ≤ 0.002651329826 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12598 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12598 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035955171469 * 1.62488E-7 / (0.000253956007 : ℝ) := by gcongr
    _ ≤ 0.002651329826 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12598 BstLean.Part154.csC Θ ≤ 0.002942203192 + 0.000669946820 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12598 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035955171469 : ℝ) * ((2 * Θ * 0.000253956400 +
        (6863 / 10000) * 0.000253956400 * 12598 * 0.001015890094) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002942203192 + 0.000669946820 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12598 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12598 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12598 0.011 Θ ∧ gammaRatio 12598 0.011 Θ ≤ 0.000087303643 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12598 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035955171469 : ℝ) * 0.525 / ((1 - 0.011) * 12598) := by gcongr
      _ ≤ (0.000087303643 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12598 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12598 0.011 Θ) :=
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
    badAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12598 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12598 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12598 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12598 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12598 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12598 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12598 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12598 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12598 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12598 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035955171469 : ℝ) * 12598 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003617172714 + 0.003321276646 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12598

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12598
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12598 BstLean.Part154.csC) (piBar (rhoBar 12598 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12598 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12598 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12598 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12598 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12598 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12598 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12598 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12598 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12598 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052698663252 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12598) ≤ 0.010639958444 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12598 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035955171469)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010639958444 + 2 * 0.737676 / 12598) := by gcongr
    _ ≤ (0.052698663252 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12598 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12598

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12598
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498918201 : ℝ) ≤ plow 12598 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12598) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867442954)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391948159) : eMP 12598 0.011 xi bn ≤ 0.001198191679 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12598 : ℝ) * (1 - 0.011))) ≤ 0.000592430683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391948159 / (12598 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592430683 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592430683 : ℝ) + 3.141593 * 0.052867442954 / (12598 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198191679 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867442954)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391948159) : PiBarMP 12598 12 0.011 xi bn ≤ 0.161909038816 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12598 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037308821464 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.621781028614 : ℝ) ≤ √((12598 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.240812541606 : ℝ) ≤ √(12598 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12598) ≤ 0.124129609786 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037308821464 + 0.052867442954 * 1.772454 / (2 * (111.621781028614 : ℝ))) * (1 + 0.001198191679) +
        8 / (12598 * 112.240812541606) + 0.124129609786 := by gcongr
    _ ≤ (0.161909038816 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867442954)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391948159) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282627876172) :
    parallelOracle 12598 0.011 xi bn cd ≤ 0.162907582916 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12598 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12598 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498918201 : ℝ) ≤ plow 12598 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.240812541606 : ℝ) ≤ √(12598 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282627876172 : ℝ) / (2 * 0.560498918201 * 112.240812541606)) * 0.161909038816 +
        0.282627876172 ^ 2 / (2 * 0.560498918201 * 112.240812541606) := by gcongr
    _ ≤ (0.162907582916 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867442954) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391948159)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282627876172) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12598 12598 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498918201 : ℝ) ≤ plow 12598 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.240812541606 : ℝ) ≤ √(12598 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12598 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12598 Θ 1.22 ≤ 0.011814779936 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.240812541606 := by gcongr <;> linarith
      _ ≤ (0.011814779936 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12598 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12598 12598 0.011 ≤ 0.008516394681 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12598 12598 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12598 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12598 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12598 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12598 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162907582916 + 0.011814779936 + (0.008516394681 : ℝ) *
        (1 + 2 * (0.282627876172 + 0.011814779936) / (0.560498918201 * 112.240812541606))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12598]

end BstLean.Part269.N12598

/-! The original eight local profiles supply actual 12598 moment certificates. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12598 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867442954 ∧
    0 ≤ bN 12598 BstLean.Part154.csC (groupTheta g) ∧ bN 12598 BstLean.Part154.csC (groupTheta g) ≤ 0.001391948159 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12598 12598 0.011
      (momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12598 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12598 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12598 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229929212920 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12598 0.011
      (momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12598 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12598
/-! The actual computed-centre upper energy formula at 12598. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12598

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12598)
open BstLean.Part268 (cell12598)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085793557685
  | 2 => 0.086742013969
  | 3 => 0.087689463975
  | 4 => 0.088637520928
  | 5 => 0.089588129393
  | 6 => 0.090543613605
  | 7 => 0.091506730191
  | 8 => 0.092480725286
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12598 12598 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12598 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12598

/-! Actual upper energy certificates on all 43 source endpoints at 12598. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12598)
open BstLean.Part268 (cell12598)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12598 (gMinus 12598) (1 - (cell12598 i).lower) ≤ 1 ∧
    energyUpper 12598 (gMinus 12598) (BstLean.Part211.gPlus 12598)
      (finiteEnergy 12598 12598 0.011) (1 - (cell12598 i).lower) ≤
      (cell12598 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨10,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨11,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨12,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨13,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨14,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨15,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨16,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨17,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨18,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨19,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨20,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨21,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨22,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨23,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨24,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨25,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨26,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨27,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨28,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨29,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨30,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨31,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨32,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨33,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨34,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨35,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨36,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨37,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨38,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨39,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨40,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨41,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨42,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨43,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨44,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨45,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨46,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨47,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨48,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨49,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨50,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨51,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12598) (by norm_num)
        (q := 1 - (cell12598 ⟨52,by decide⟩).lower)
        (by norm_num [cell12598]) (by norm_num [cell12598])
      exact ⟨E.1,E.2.trans (by norm_num [cell12598])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12598

/-! Source-cell containment and simple scalar guards at 12598. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12598)
open BstLean.Part268 (cell12598)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12598 ⟨10,by decide⟩).lower ∧ (cell12598 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12598 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12598 ⟨11,by decide⟩).lower ∧ (cell12598 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12598 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12598 ⟨12,by decide⟩).lower ∧ (cell12598 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12598 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12598 ⟨13,by decide⟩).lower ∧ (cell12598 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12598 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12598 ⟨14,by decide⟩).lower ∧ (cell12598 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12598 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12598 ⟨15,by decide⟩).lower ∧ (cell12598 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12598 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12598 ⟨16,by decide⟩).lower ∧ (cell12598 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12598 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12598 ⟨17,by decide⟩).lower ∧ (cell12598 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12598 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12598 ⟨18,by decide⟩).lower ∧ (cell12598 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12598 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12598 ⟨19,by decide⟩).lower ∧ (cell12598 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12598 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12598 ⟨20,by decide⟩).lower ∧ (cell12598 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12598 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12598 ⟨21,by decide⟩).lower ∧ (cell12598 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12598 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12598 ⟨22,by decide⟩).lower ∧ (cell12598 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12598 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12598 ⟨23,by decide⟩).lower ∧ (cell12598 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12598 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12598 ⟨24,by decide⟩).lower ∧ (cell12598 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12598 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12598 ⟨25,by decide⟩).lower ∧ (cell12598 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12598 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12598 ⟨26,by decide⟩).lower ∧ (cell12598 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12598 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12598 ⟨27,by decide⟩).lower ∧ (cell12598 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12598 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12598 ⟨28,by decide⟩).lower ∧ (cell12598 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12598 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12598 ⟨29,by decide⟩).lower ∧ (cell12598 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12598 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12598 ⟨30,by decide⟩).lower ∧ (cell12598 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12598 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12598 ⟨31,by decide⟩).lower ∧ (cell12598 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12598 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12598 ⟨32,by decide⟩).lower ∧ (cell12598 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12598 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12598 ⟨33,by decide⟩).lower ∧ (cell12598 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12598 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12598 ⟨34,by decide⟩).lower ∧ (cell12598 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12598 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12598 ⟨35,by decide⟩).lower ∧ (cell12598 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12598 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12598 ⟨36,by decide⟩).lower ∧ (cell12598 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12598 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12598 ⟨37,by decide⟩).lower ∧ (cell12598 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12598 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12598 ⟨38,by decide⟩).lower ∧ (cell12598 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12598 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12598 ⟨39,by decide⟩).lower ∧ (cell12598 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12598 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12598 ⟨40,by decide⟩).lower ∧ (cell12598 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12598 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12598 ⟨41,by decide⟩).lower ∧ (cell12598 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12598 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12598 ⟨42,by decide⟩).lower ∧ (cell12598 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12598 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12598 ⟨43,by decide⟩).lower ∧ (cell12598 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12598 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12598 ⟨44,by decide⟩).lower ∧ (cell12598 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12598 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12598 ⟨45,by decide⟩).lower ∧ (cell12598 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12598 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12598 ⟨46,by decide⟩).lower ∧ (cell12598 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12598 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12598 ⟨47,by decide⟩).lower ∧ (cell12598 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12598 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12598 ⟨48,by decide⟩).lower ∧ (cell12598 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12598 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12598 ⟨49,by decide⟩).lower ∧ (cell12598 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12598 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12598 ⟨50,by decide⟩).lower ∧ (cell12598 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12598 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12598 ⟨51,by decide⟩).lower ∧ (cell12598 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12598 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12598 ⟨52,by decide⟩).lower ∧ (cell12598 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12598 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12598 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12598 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12598,cell12598,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12598 i).lower ∧
    (cell12598 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12598 i).upper ≤ (0.532 : ℝ) ∧
    (cell12598 i).centre ≤ (0.1 : ℝ) ∧ (cell12598 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12598 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12598 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12598

/-! The local source numeric instances at 12598 have no network premises. -/
namespace BstLean.Part269.N12598
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12598)
open BstLean.Part268 (cell12598)

noncomputable def sourceNumerics12598 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12598 (cell12598 i)
      scalarRow12598.M scalarRow12598.H scalarRow12598.xi := by
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
    energy_allowance := scalarRow12598.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12598]
    centre_nonneg := (scalarRow12598.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12598])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12598
/-! Actual 12599 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12599 ≤ (1.035953731935 : ℝ) := by
  have hr : (112.245267160802 : ℝ) ≤ √(12599 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.245267160802 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12599 12599 (11 / 1000) ≤
    (0.008516056692 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12599) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.245267160802 : ℝ) ≤ √(12599 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12599)
  have hdiv : K / √(12599 : ℝ) ≤ K / 112.245267160802 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.245267160802 ≤ (0.008516056692 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12599.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12599 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12599 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12599 := gPlus_lower 12599
end BstLean.Part269.N12599

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12599
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035953731934 : ℝ) ≤ wn 12599 := by
  have hn : √(12599 : ℝ) ≤ 112.245267160803 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12599 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.245267160803 ≤ 2 / √(12599 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253935497 : ℝ) ≤ rhoBar 12599 BstLean.Part154.csC ∧
    rhoBar 12599 BstLean.Part154.csC ≤ 0.000253935890 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035953731934 : ℝ) / (1.295212 * 12599) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035953731935 : ℝ) / (1.29521 * 12599) := by gcongr
      _ ≤ (0.000253935890 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12599 BstLean.Part154.csC) ≤ 0.001015808044 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12599 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) ≤ 0.000193958019 ∧
    cc1 (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) ≤ 0.000123416760 ∧
    cc2 (rhoBar 12599 BstLean.Part154.csC) ≤ 0.000071644357 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12599 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12599 BstLean.Part154.csC * nuR (rhoBar 12599 BstLean.Part154.csC)) ≤ 0.000507887901 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253935890 : ℝ) * 0.001015808044 := by gcongr
      _ ≤ (0.000507887901 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12599 BstLean.Part154.csC) * nuR (rhoBar 12599 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001015808044 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12599 BstLean.Part154.csC) * rhoBar 12599 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253935890 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253935890 / 2 + 0.399 * 0.001015808044 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193958019 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507887901 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123416760 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253935890 / 1.414213562 := by gcongr
      _ ≤ (0.000071644357 : ℝ) := by norm_num

end BstLean.Part269.N12599

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12599
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) ≤ 1.62462E-7 := by
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12599 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12599 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193958019 : ℝ) ^ 2 + 0.000123416760 ^ 2 + 3 * 0.000071644357 ^ 2 +
        2 * 0.797885 * 0.000193958019 * 0.000123416760 + 2 * 0.000193958019 * 0.000071644357 +
        4 * 0.797885 * 0.000123416760 * 0.000071644357 := by gcongr
    _ ≤ (1.62462E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12599 BstLean.Part154.csC Θ ≤ 0.002651116007 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12599 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12599 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035953731935 * 1.62462E-7 / (0.000253935497 : ℝ) := by gcongr
    _ ≤ 0.002651116007 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12599 BstLean.Part154.csC Θ ≤ 0.002941957381 + 0.000669891783 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12599 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035953731935 : ℝ) * ((2 * Θ * 0.000253935890 +
        (6863 / 10000) * 0.000253935890 * 12599 * 0.001015808044) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002941957381 + 0.000669891783 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12599 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12599 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12599 0.011 Θ ∧ gammaRatio 12599 0.011 Θ ≤ 0.000087296593 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12599 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035953731935 : ℝ) * 0.525 / ((1 - 0.011) * 12599) := by gcongr
      _ ≤ (0.000087296593 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12599 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12599 0.011 Θ) :=
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
    badAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12599 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12599 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12599 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12599 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12599 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12599 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12599 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12599 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12599 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12599 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035953731935 : ℝ) * 12599 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003616926903 + 0.003321007790 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12599

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12599
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12599 BstLean.Part154.csC) (piBar (rhoBar 12599 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12599 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12599 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12599 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12599 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12599 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12599 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12599 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12599 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12599 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052696549057 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12599) ≤ 0.010639536181 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12599 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035953731935)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010639536181 + 2 * 0.737676 / 12599) := by gcongr
    _ ≤ (0.052696549057 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12599 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12599

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12599
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498964155 : ℝ) ≤ plow 12599 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12599) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867055993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391835904) : eMP 12599 0.011 xi bn ≤ 0.001198095723 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12599 : ℝ) * (1 - 0.011))) ≤ 0.000592383283 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001391835904 / (12599 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592383283 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592383283 : ℝ) + 3.141593 * 0.052867055993 / (12599 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001198095723 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867055993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391835904) : PiBarMP 12599 12 0.011 xi bn ≤ 0.161902582266 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12599 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037307317031 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.626211079656 : ℝ) ≤ √((12599 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.245267160802 : ℝ) ≤ √(12599 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12599) ≤ 0.124124683519 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037307317031 + 0.052867055993 * 1.772454 / (2 * (111.626211079656 : ℝ))) * (1 + 0.001198095723) +
        8 / (12599 * 112.245267160802) + 0.124124683519 := by gcongr
    _ ≤ (0.161902582266 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867055993)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391835904) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282624920497) :
    parallelOracle 12599 0.011 xi bn cd ≤ 0.162901055072 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12599 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12599 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498964155 : ℝ) ≤ plow 12599 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.245267160802 : ℝ) ≤ √(12599 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282624920497 : ℝ) / (2 * 0.560498964155 * 112.245267160802)) * 0.161902582266 +
        0.282624920497 ^ 2 / (2 * 0.560498964155 * 112.245267160802) := by gcongr
    _ ≤ (0.162901055072 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052867055993) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001391835904)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282624920497) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12599 12599 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498964155 : ℝ) ≤ plow 12599 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.245267160802 : ℝ) ≤ √(12599 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12599 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12599 Θ 1.22 ≤ 0.011814311049 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.245267160802 := by gcongr <;> linarith
      _ ≤ (0.011814311049 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12599 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12599 12599 0.011 ≤ 0.008516056692 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12599 12599 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12599 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12599 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12599 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12599 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162901055072 + 0.011814311049 + (0.008516056692 : ℝ) *
        (1 + 2 * (0.282624920497 + 0.011814311049) / (0.560498964155 * 112.245267160802))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12599]

end BstLean.Part269.N12599

/-! The original eight local profiles supply actual 12599 moment certificates. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12599 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052867055993 ∧
    0 ≤ bN 12599 BstLean.Part154.csC (groupTheta g) ∧ bN 12599 BstLean.Part154.csC (groupTheta g) ≤ 0.001391835904 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12599 12599 0.011
      (momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12599 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12599 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12599 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229928371440 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12599 0.011
      (momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12599 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12599
/-! The actual computed-centre upper energy formula at 12599. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12599

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12599)
open BstLean.Part268 (cell12599)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085790525460
  | 2 => 0.086738923338
  | 3 => 0.087686305988
  | 4 => 0.088634284607
  | 5 => 0.089584801376
  | 6 => 0.090540177754
  | 7 => 0.091503167150
  | 8 => 0.092477011993
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12599 12599 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12599 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12599

/-! Actual upper energy certificates on all 43 source endpoints at 12599. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12599)
open BstLean.Part268 (cell12599)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12599 (gMinus 12599) (1 - (cell12599 i).lower) ≤ 1 ∧
    energyUpper 12599 (gMinus 12599) (BstLean.Part211.gPlus 12599)
      (finiteEnergy 12599 12599 0.011) (1 - (cell12599 i).lower) ≤
      (cell12599 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨10,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨11,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨12,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨13,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨14,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨15,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨16,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨17,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨18,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨19,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨20,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨21,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨22,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨23,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨24,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨25,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨26,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨27,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨28,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨29,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨30,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨31,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨32,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨33,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨34,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨35,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨36,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨37,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨38,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨39,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨40,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨41,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨42,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨43,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨44,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨45,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨46,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨47,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨48,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨49,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨50,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨51,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12599) (by norm_num)
        (q := 1 - (cell12599 ⟨52,by decide⟩).lower)
        (by norm_num [cell12599]) (by norm_num [cell12599])
      exact ⟨E.1,E.2.trans (by norm_num [cell12599])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12599

/-! Source-cell containment and simple scalar guards at 12599. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12599)
open BstLean.Part268 (cell12599)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12599 ⟨10,by decide⟩).lower ∧ (cell12599 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12599 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12599 ⟨11,by decide⟩).lower ∧ (cell12599 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12599 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12599 ⟨12,by decide⟩).lower ∧ (cell12599 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12599 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12599 ⟨13,by decide⟩).lower ∧ (cell12599 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12599 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12599 ⟨14,by decide⟩).lower ∧ (cell12599 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12599 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12599 ⟨15,by decide⟩).lower ∧ (cell12599 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12599 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12599 ⟨16,by decide⟩).lower ∧ (cell12599 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12599 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12599 ⟨17,by decide⟩).lower ∧ (cell12599 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12599 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12599 ⟨18,by decide⟩).lower ∧ (cell12599 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12599 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12599 ⟨19,by decide⟩).lower ∧ (cell12599 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12599 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12599 ⟨20,by decide⟩).lower ∧ (cell12599 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12599 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12599 ⟨21,by decide⟩).lower ∧ (cell12599 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12599 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12599 ⟨22,by decide⟩).lower ∧ (cell12599 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12599 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12599 ⟨23,by decide⟩).lower ∧ (cell12599 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12599 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12599 ⟨24,by decide⟩).lower ∧ (cell12599 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12599 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12599 ⟨25,by decide⟩).lower ∧ (cell12599 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12599 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12599 ⟨26,by decide⟩).lower ∧ (cell12599 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12599 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12599 ⟨27,by decide⟩).lower ∧ (cell12599 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12599 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12599 ⟨28,by decide⟩).lower ∧ (cell12599 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12599 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12599 ⟨29,by decide⟩).lower ∧ (cell12599 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12599 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12599 ⟨30,by decide⟩).lower ∧ (cell12599 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12599 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12599 ⟨31,by decide⟩).lower ∧ (cell12599 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12599 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12599 ⟨32,by decide⟩).lower ∧ (cell12599 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12599 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12599 ⟨33,by decide⟩).lower ∧ (cell12599 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12599 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12599 ⟨34,by decide⟩).lower ∧ (cell12599 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12599 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12599 ⟨35,by decide⟩).lower ∧ (cell12599 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12599 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12599 ⟨36,by decide⟩).lower ∧ (cell12599 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12599 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12599 ⟨37,by decide⟩).lower ∧ (cell12599 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12599 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12599 ⟨38,by decide⟩).lower ∧ (cell12599 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12599 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12599 ⟨39,by decide⟩).lower ∧ (cell12599 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12599 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12599 ⟨40,by decide⟩).lower ∧ (cell12599 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12599 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12599 ⟨41,by decide⟩).lower ∧ (cell12599 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12599 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12599 ⟨42,by decide⟩).lower ∧ (cell12599 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12599 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12599 ⟨43,by decide⟩).lower ∧ (cell12599 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12599 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12599 ⟨44,by decide⟩).lower ∧ (cell12599 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12599 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12599 ⟨45,by decide⟩).lower ∧ (cell12599 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12599 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12599 ⟨46,by decide⟩).lower ∧ (cell12599 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12599 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12599 ⟨47,by decide⟩).lower ∧ (cell12599 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12599 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12599 ⟨48,by decide⟩).lower ∧ (cell12599 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12599 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12599 ⟨49,by decide⟩).lower ∧ (cell12599 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12599 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12599 ⟨50,by decide⟩).lower ∧ (cell12599 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12599 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12599 ⟨51,by decide⟩).lower ∧ (cell12599 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12599 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12599 ⟨52,by decide⟩).lower ∧ (cell12599 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12599 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12599 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12599 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12599,cell12599,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12599 i).lower ∧
    (cell12599 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12599 i).upper ≤ (0.532 : ℝ) ∧
    (cell12599 i).centre ≤ (0.1 : ℝ) ∧ (cell12599 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12599 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12599 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12599

/-! The local source numeric instances at 12599 have no network premises. -/
namespace BstLean.Part269.N12599
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12599)
open BstLean.Part268 (cell12599)

noncomputable def sourceNumerics12599 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12599 (cell12599 i)
      scalarRow12599.M scalarRow12599.H scalarRow12599.xi := by
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
    energy_allowance := scalarRow12599.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12599]
    centre_nonneg := (scalarRow12599.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12599])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12599