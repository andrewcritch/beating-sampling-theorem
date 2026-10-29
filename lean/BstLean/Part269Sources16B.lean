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
import BstLean.Part269Direction16
import BstLean.Part269Shared16
import BstLean.Part269Finite
import BstLean.Part269Rows16
import BstLean.Part269Source
/-! Actual 12763 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12763 ≤ (1.035719955562 : ℝ) := by
  have hr : (112.973448207974 : ℝ) ≤ √(12763 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.973448207974 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12763 12763 (11 / 1000) ≤
    (0.008461165222 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12763) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.973448207974 : ℝ) ≤ √(12763 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12763)
  have hdiv : K / √(12763 : ℝ) ≤ K / 112.973448207974 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.973448207974 ≤ (0.008461165222 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12763.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12763 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12763 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12763 := gPlus_lower 12763
end BstLean.Part269.N12763

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12763
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035719955561 : ℝ) ≤ wn 12763 := by
  have hn : √(12763 : ℝ) ≤ 112.973448207975 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12763 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.973448207975 ≤ 2 / √(12763 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250615949 : ℝ) ≤ rhoBar 12763 BstLean.Part154.csC ∧
    rhoBar 12763 BstLean.Part154.csC ≤ 0.000250616337 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035719955561 : ℝ) / (1.295212 * 12763) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035719955562 : ℝ) / (1.29521 * 12763) := by gcongr
      _ ≤ (0.000250616337 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12763 BstLean.Part154.csC) ≤ 0.001002528157 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12763 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) ≤ 0.000191422404 ∧
    cc1 (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) ≤ 0.000121803356 ∧
    cc2 (rhoBar 12763 BstLean.Part154.csC) ≤ 0.000070707793 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12763 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12763 BstLean.Part154.csC * nuR (rhoBar 12763 BstLean.Part154.csC)) ≤ 0.000501248377 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250616337 : ℝ) * 0.001002528157 := by gcongr
      _ ≤ (0.000501248377 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12763 BstLean.Part154.csC) * nuR (rhoBar 12763 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002528157 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12763 BstLean.Part154.csC) * rhoBar 12763 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250616337 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250616337 / 2 + 0.399 * 0.001002528157 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191422404 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501248377 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121803356 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250616337 / 1.414213562 := by gcongr
      _ ≤ (0.000070707793 : ℝ) := by norm_num

end BstLean.Part269.N12763

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12763
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) ≤ 1.58242E-7 := by
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12763 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12763 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191422404 : ℝ) ^ 2 + 0.000121803356 ^ 2 + 3 * 0.000070707793 ^ 2 +
        2 * 0.797885 * 0.000191422404 * 0.000121803356 + 2 * 0.000191422404 * 0.000070707793 +
        4 * 0.797885 * 0.000121803356 * 0.000070707793 := by gcongr
    _ ≤ (1.58242E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12763 BstLean.Part154.csC Θ ≤ 0.002615865397 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12763 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12763 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035719955562 * 1.58242E-7 / (0.000250615949 : ℝ) := by gcongr
    _ ≤ 0.002615865397 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12763 BstLean.Part154.csC Θ ≤ 0.002902186238 + 0.000660985492 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12763 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035719955562 : ℝ) * ((2 * Θ * 0.000250616337 +
        (6863 / 10000) * 0.000250616337 * 12763 * 0.001002528157) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002902186238 + 0.000660985492 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12763 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12763 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12763 0.011 Θ ∧ gammaRatio 12763 0.011 Θ ≤ 0.000086155416 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12763 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035719955562 : ℝ) * 0.525 / ((1 - 0.011) * 12763) := by gcongr
      _ ≤ (0.000086155416 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12763 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12763 0.011 Θ) :=
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
    badAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12763 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12763 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12763 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12763 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12763 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12763 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12763 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12763 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12763 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12763 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035719955562 : ℝ) * 12763 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003462347708 + 0.003276850889 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12763

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12763
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12763 BstLean.Part154.csC) (piBar (rhoBar 12763 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12763 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12763 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12763 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12763 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12763 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12763 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12763 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12763 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12763 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052353214628 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12763) ≤ 0.010570958044 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12763 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035719955562)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010570958044 + 2 * 0.737676 / 12763) := by gcongr
    _ ≤ (0.052353214628 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12763 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12763

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12763
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506403275 : ℝ) ≤ plow 12763 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12763) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689294425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373329334) : eMP 12763 0.011 xi bn ≤ 0.001182391628 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12763 : ℝ) * (1 - 0.011))) ≤ 0.000584638994 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373329334 / (12763 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584638994 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584638994 : ℝ) + 3.141593 * 0.052689294425 / (12763 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182391628 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689294425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373329334) : PiBarMP 12763 12 0.011 xi bn ≤ 0.160848558353 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12763 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037058458333 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.350376056335 : ℝ) ≤ √((12763 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.973448207974 : ℝ) ≤ √(12763 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12763) ≤ 0.123324626129 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037058458333 + 0.052689294425 * 1.772454 / (2 * (112.350376056335 : ℝ))) * (1 + 0.001182391628) +
        8 / (12763 * 112.973448207974) + 0.123324626129 := by gcongr
    _ ≤ (0.160848558353 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689294425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373329334) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281894702001) :
    parallelOracle 12763 0.011 xi bn cd ≤ 0.161834047655 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12763 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12763 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506403275 : ℝ) ≤ plow 12763 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.973448207974 : ℝ) ≤ √(12763 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281894702001 : ℝ) / (2 * 0.560506403275 * 112.973448207974)) * 0.160848558353 +
        0.281894702001 ^ 2 / (2 * 0.560506403275 * 112.973448207974) := by gcongr
    _ ≤ (0.161834047655 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689294425) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373329334)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281894702001) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12763 12763 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506403275 : ℝ) ≤ plow 12763 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.973448207974 : ℝ) ≤ √(12763 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12763 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12763 Θ 1.22 ≤ 0.011738160790 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.973448207974 := by gcongr <;> linarith
      _ ≤ (0.011738160790 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12763 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12763 12763 0.011 ≤ 0.008461165222 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12763 12763 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12763 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12763 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12763 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12763 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161834047655 + 0.011738160790 + (0.008461165222 : ℝ) *
        (1 + 2 * (0.281894702001 + 0.011738160790) / (0.560506403275 * 112.973448207974))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12763]

end BstLean.Part269.N12763

/-! The original eight local profiles supply actual 12763 moment certificates. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12763 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052689294425 ∧
    0 ≤ bN 12763 BstLean.Part154.csC (groupTheta g) ∧ bN 12763 BstLean.Part154.csC (groupTheta g) ≤ 0.001373329334 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12763 12763 0.011
      (momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12763 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12763 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12763 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229541487373 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12763 0.011
      (momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12763 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12763
/-! The actual computed-centre upper energy formula at 12763. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12763

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12763)
open BstLean.Part268 (cell12763)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085308635898
  | 2 => 0.086248095648
  | 3 => 0.087185222811
  | 4 => 0.088121326129
  | 5 => 0.089057992116
  | 6 => 0.089997126767
  | 7 => 0.090941001281
  | 8 => 0.091892301838
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12763 12763 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12763 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12763

/-! Actual upper energy certificates on all 43 source endpoints at 12763. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12763)
open BstLean.Part268 (cell12763)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12763 (gMinus 12763) (1 - (cell12763 i).lower) ≤ 1 ∧
    energyUpper 12763 (gMinus 12763) (BstLean.Part211.gPlus 12763)
      (finiteEnergy 12763 12763 0.011) (1 - (cell12763 i).lower) ≤
      (cell12763 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨10,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨11,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨12,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨13,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨14,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨15,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨16,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨17,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨18,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨19,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨20,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨21,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨22,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨23,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨24,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨25,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨26,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨27,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨28,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨29,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨30,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨31,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨32,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨33,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨34,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨35,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨36,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨37,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨38,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨39,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨40,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨41,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨42,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨43,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨44,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨45,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨46,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨47,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨48,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨49,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨50,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨51,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12763) (by norm_num)
        (q := 1 - (cell12763 ⟨52,by decide⟩).lower)
        (by norm_num [cell12763]) (by norm_num [cell12763])
      exact ⟨E.1,E.2.trans (by norm_num [cell12763])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12763

/-! Source-cell containment and simple scalar guards at 12763. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12763)
open BstLean.Part268 (cell12763)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12763 ⟨10,by decide⟩).lower ∧ (cell12763 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12763 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12763 ⟨11,by decide⟩).lower ∧ (cell12763 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12763 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12763 ⟨12,by decide⟩).lower ∧ (cell12763 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12763 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12763 ⟨13,by decide⟩).lower ∧ (cell12763 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12763 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12763 ⟨14,by decide⟩).lower ∧ (cell12763 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12763 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12763 ⟨15,by decide⟩).lower ∧ (cell12763 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12763 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12763 ⟨16,by decide⟩).lower ∧ (cell12763 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12763 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12763 ⟨17,by decide⟩).lower ∧ (cell12763 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12763 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12763 ⟨18,by decide⟩).lower ∧ (cell12763 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12763 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12763 ⟨19,by decide⟩).lower ∧ (cell12763 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12763 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12763 ⟨20,by decide⟩).lower ∧ (cell12763 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12763 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12763 ⟨21,by decide⟩).lower ∧ (cell12763 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12763 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12763 ⟨22,by decide⟩).lower ∧ (cell12763 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12763 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12763 ⟨23,by decide⟩).lower ∧ (cell12763 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12763 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12763 ⟨24,by decide⟩).lower ∧ (cell12763 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12763 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12763 ⟨25,by decide⟩).lower ∧ (cell12763 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12763 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12763 ⟨26,by decide⟩).lower ∧ (cell12763 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12763 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12763 ⟨27,by decide⟩).lower ∧ (cell12763 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12763 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12763 ⟨28,by decide⟩).lower ∧ (cell12763 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12763 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12763 ⟨29,by decide⟩).lower ∧ (cell12763 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12763 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12763 ⟨30,by decide⟩).lower ∧ (cell12763 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12763 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12763 ⟨31,by decide⟩).lower ∧ (cell12763 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12763 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12763 ⟨32,by decide⟩).lower ∧ (cell12763 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12763 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12763 ⟨33,by decide⟩).lower ∧ (cell12763 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12763 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12763 ⟨34,by decide⟩).lower ∧ (cell12763 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12763 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12763 ⟨35,by decide⟩).lower ∧ (cell12763 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12763 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12763 ⟨36,by decide⟩).lower ∧ (cell12763 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12763 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12763 ⟨37,by decide⟩).lower ∧ (cell12763 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12763 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12763 ⟨38,by decide⟩).lower ∧ (cell12763 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12763 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12763 ⟨39,by decide⟩).lower ∧ (cell12763 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12763 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12763 ⟨40,by decide⟩).lower ∧ (cell12763 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12763 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12763 ⟨41,by decide⟩).lower ∧ (cell12763 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12763 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12763 ⟨42,by decide⟩).lower ∧ (cell12763 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12763 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12763 ⟨43,by decide⟩).lower ∧ (cell12763 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12763 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12763 ⟨44,by decide⟩).lower ∧ (cell12763 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12763 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12763 ⟨45,by decide⟩).lower ∧ (cell12763 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12763 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12763 ⟨46,by decide⟩).lower ∧ (cell12763 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12763 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12763 ⟨47,by decide⟩).lower ∧ (cell12763 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12763 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12763 ⟨48,by decide⟩).lower ∧ (cell12763 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12763 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12763 ⟨49,by decide⟩).lower ∧ (cell12763 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12763 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12763 ⟨50,by decide⟩).lower ∧ (cell12763 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12763 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12763 ⟨51,by decide⟩).lower ∧ (cell12763 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12763 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12763 ⟨52,by decide⟩).lower ∧ (cell12763 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12763 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12763 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12763 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12763,cell12763,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12763 i).lower ∧
    (cell12763 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12763 i).upper ≤ (0.532 : ℝ) ∧
    (cell12763 i).centre ≤ (0.1 : ℝ) ∧ (cell12763 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12763 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12763 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12763

/-! The local source numeric instances at 12763 have no network premises. -/
namespace BstLean.Part269.N12763
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12763)
open BstLean.Part268 (cell12763)

noncomputable def sourceNumerics12763 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12763 (cell12763 i)
      scalarRow12763.M scalarRow12763.H scalarRow12763.xi := by
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
    energy_allowance := scalarRow12763.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12763]
    centre_nonneg := (scalarRow12763.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12763])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12763
/-! Actual 12764 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12764 ≤ (1.035718544012 : ℝ) := by
  have hr : (112.977873939988 : ℝ) ≤ √(12764 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.977873939988 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12764 12764 (11 / 1000) ≤
    (0.008460833766 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12764) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.977873939988 : ℝ) ≤ √(12764 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12764)
  have hdiv : K / √(12764 : ℝ) ≤ K / 112.977873939988 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.977873939988 ≤ (0.008460833766 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12764.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12764 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12764 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12764 := gPlus_lower 12764
end BstLean.Part269.N12764

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12764
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035718544011 : ℝ) ≤ wn 12764 := by
  have hn : √(12764 : ℝ) ≤ 112.977873939989 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12764 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.977873939989 ≤ 2 / √(12764 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250595973 : ℝ) ≤ rhoBar 12764 BstLean.Part154.csC ∧
    rhoBar 12764 BstLean.Part154.csC ≤ 0.000250596361 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035718544011 : ℝ) / (1.295212 * 12764) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035718544012 : ℝ) / (1.29521 * 12764) := by gcongr
      _ ≤ (0.000250596361 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12764 BstLean.Part154.csC) ≤ 0.001002448243 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12764 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) ≤ 0.000191407146 ∧
    cc1 (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) ≤ 0.000121793647 ∧
    cc2 (rhoBar 12764 BstLean.Part154.csC) ≤ 0.000070702157 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12764 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12764 BstLean.Part154.csC * nuR (rhoBar 12764 BstLean.Part154.csC)) ≤ 0.000501208422 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250596361 : ℝ) * 0.001002448243 := by gcongr
      _ ≤ (0.000501208422 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12764 BstLean.Part154.csC) * nuR (rhoBar 12764 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002448243 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12764 BstLean.Part154.csC) * rhoBar 12764 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250596361 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250596361 / 2 + 0.399 * 0.001002448243 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191407146 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501208422 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121793647 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250596361 / 1.414213562 := by gcongr
      _ ≤ (0.000070702157 : ℝ) := by norm_num

end BstLean.Part269.N12764

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12764
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) ≤ 1.58217E-7 := by
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12764 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12764 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191407146 : ℝ) ^ 2 + 0.000121793647 ^ 2 + 3 * 0.000070702157 ^ 2 +
        2 * 0.797885 * 0.000191407146 * 0.000121793647 + 2 * 0.000191407146 * 0.000070702157 +
        4 * 0.797885 * 0.000121793647 * 0.000070702157 := by gcongr
    _ ≤ (1.58217E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12764 BstLean.Part154.csC Θ ≤ 0.002615657051 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12764 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12764 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035718544012 * 1.58217E-7 / (0.000250595973 : ℝ) := by gcongr
    _ ≤ 0.002615657051 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12764 BstLean.Part154.csC Θ ≤ 0.002901946989 + 0.000660931905 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12764 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035718544012 : ℝ) * ((2 * Θ * 0.000250596361 +
        (6863 / 10000) * 0.000250596361 * 12764 * 0.001002448243) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002901946989 + 0.000660931905 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12764 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12764 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12764 0.011 Θ ∧ gammaRatio 12764 0.011 Θ ≤ 0.000086148549 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12764 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035718544012 : ℝ) * 0.525 / ((1 - 0.011) * 12764) := by gcongr
      _ ≤ (0.000086148549 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12764 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12764 0.011 Θ) :=
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
    badAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12764 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12764 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12764 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12764 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12764 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12764 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12764 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12764 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12764 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12764 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035718544012 : ℝ) * 12764 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003462108459 + 0.003276588956 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12764

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12764
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12764 BstLean.Part154.csC) (piBar (rhoBar 12764 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12764 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12764 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12764 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12764 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12764 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12764 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12764 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12764 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12764 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052351141588 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12764) ≤ 0.010570543943 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12764 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035718544012)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010570543943 + 2 * 0.737676 / 12764) := by gcongr
    _ ≤ (0.052351141588 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12764 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12764

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12764
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506448049 : ℝ) ≤ plow 12764 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12764) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688917661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373219952) : eMP 12764 0.011 xi bn ≤ 0.001182298139 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12764 : ℝ) * (1 - 0.011))) ≤ 0.000584592810 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373219952 / (12764 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584592810 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584592810 : ℝ) + 3.141593 * 0.052688917661 / (12764 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182298139 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688917661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373219952) : PiBarMP 12764 12 0.011 xi bn ≤ 0.160842226295 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12764 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037056982500 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.354777379513 : ℝ) ≤ √((12764 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.977873939988 : ℝ) ≤ √(12764 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12764) ≤ 0.123319795080 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037056982500 + 0.052688917661 * 1.772454 / (2 * (112.354777379513 : ℝ))) * (1 + 0.001182298139) +
        8 / (12764 * 112.977873939988) + 0.123319795080 := by gcongr
    _ ≤ (0.160842226295 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688917661)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373219952) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281891808271) :
    parallelOracle 12764 0.011 xi bn cd ≤ 0.161827646263 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12764 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12764 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506448049 : ℝ) ≤ plow 12764 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.977873939988 : ℝ) ≤ √(12764 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281891808271 : ℝ) / (2 * 0.560506448049 * 112.977873939988)) * 0.160842226295 +
        0.281891808271 ^ 2 / (2 * 0.560506448049 * 112.977873939988) := by gcongr
    _ ≤ (0.161827646263 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688917661) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373219952)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281891808271) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12764 12764 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506448049 : ℝ) ≤ plow 12764 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.977873939988 : ℝ) ≤ √(12764 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12764 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12764 Θ 1.22 ≤ 0.011737700966 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.977873939988 := by gcongr <;> linarith
      _ ≤ (0.011737700966 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12764 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12764 12764 0.011 ≤ 0.008460833766 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12764 12764 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12764 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12764 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12764 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12764 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161827646263 + 0.011737700966 + (0.008460833766 : ℝ) *
        (1 + 2 * (0.281891808271 + 0.011737700966) / (0.560506448049 * 112.977873939988))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12764]

end BstLean.Part269.N12764

/-! The original eight local profiles supply actual 12764 moment certificates. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12764 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052688917661 ∧
    0 ≤ bN 12764 BstLean.Part154.csC (groupTheta g) ∧ bN 12764 BstLean.Part154.csC (groupTheta g) ≤ 0.001373219952 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12764 12764 0.011
      (momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12764 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12764 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12764 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229540666683 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12764 0.011
      (momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12764 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12764
/-! The actual computed-centre upper energy formula at 12764. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12764

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12764)
open BstLean.Part268 (cell12764)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085305786279
  | 2 => 0.086245195163
  | 3 => 0.087182264281
  | 4 => 0.088118300705
  | 5 => 0.089054888980
  | 6 => 0.089993932800
  | 7 => 0.090937700683
  | 8 => 0.091888875716
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12764 12764 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12764 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12764

/-! Actual upper energy certificates on all 43 source endpoints at 12764. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12764)
open BstLean.Part268 (cell12764)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12764 (gMinus 12764) (1 - (cell12764 i).lower) ≤ 1 ∧
    energyUpper 12764 (gMinus 12764) (BstLean.Part211.gPlus 12764)
      (finiteEnergy 12764 12764 0.011) (1 - (cell12764 i).lower) ≤
      (cell12764 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨10,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨11,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨12,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨13,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨14,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨15,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨16,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨17,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨18,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨19,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨20,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨21,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨22,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨23,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨24,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨25,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨26,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨27,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨28,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨29,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨30,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨31,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨32,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨33,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨34,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨35,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨36,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨37,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨38,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨39,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨40,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨41,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨42,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨43,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨44,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨45,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨46,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨47,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨48,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨49,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨50,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨51,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12764) (by norm_num)
        (q := 1 - (cell12764 ⟨52,by decide⟩).lower)
        (by norm_num [cell12764]) (by norm_num [cell12764])
      exact ⟨E.1,E.2.trans (by norm_num [cell12764])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12764

/-! Source-cell containment and simple scalar guards at 12764. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12764)
open BstLean.Part268 (cell12764)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12764 ⟨10,by decide⟩).lower ∧ (cell12764 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12764 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12764 ⟨11,by decide⟩).lower ∧ (cell12764 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12764 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12764 ⟨12,by decide⟩).lower ∧ (cell12764 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12764 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12764 ⟨13,by decide⟩).lower ∧ (cell12764 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12764 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12764 ⟨14,by decide⟩).lower ∧ (cell12764 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12764 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12764 ⟨15,by decide⟩).lower ∧ (cell12764 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12764 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12764 ⟨16,by decide⟩).lower ∧ (cell12764 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12764 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12764 ⟨17,by decide⟩).lower ∧ (cell12764 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12764 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12764 ⟨18,by decide⟩).lower ∧ (cell12764 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12764 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12764 ⟨19,by decide⟩).lower ∧ (cell12764 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12764 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12764 ⟨20,by decide⟩).lower ∧ (cell12764 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12764 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12764 ⟨21,by decide⟩).lower ∧ (cell12764 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12764 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12764 ⟨22,by decide⟩).lower ∧ (cell12764 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12764 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12764 ⟨23,by decide⟩).lower ∧ (cell12764 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12764 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12764 ⟨24,by decide⟩).lower ∧ (cell12764 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12764 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12764 ⟨25,by decide⟩).lower ∧ (cell12764 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12764 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12764 ⟨26,by decide⟩).lower ∧ (cell12764 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12764 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12764 ⟨27,by decide⟩).lower ∧ (cell12764 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12764 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12764 ⟨28,by decide⟩).lower ∧ (cell12764 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12764 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12764 ⟨29,by decide⟩).lower ∧ (cell12764 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12764 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12764 ⟨30,by decide⟩).lower ∧ (cell12764 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12764 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12764 ⟨31,by decide⟩).lower ∧ (cell12764 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12764 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12764 ⟨32,by decide⟩).lower ∧ (cell12764 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12764 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12764 ⟨33,by decide⟩).lower ∧ (cell12764 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12764 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12764 ⟨34,by decide⟩).lower ∧ (cell12764 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12764 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12764 ⟨35,by decide⟩).lower ∧ (cell12764 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12764 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12764 ⟨36,by decide⟩).lower ∧ (cell12764 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12764 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12764 ⟨37,by decide⟩).lower ∧ (cell12764 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12764 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12764 ⟨38,by decide⟩).lower ∧ (cell12764 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12764 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12764 ⟨39,by decide⟩).lower ∧ (cell12764 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12764 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12764 ⟨40,by decide⟩).lower ∧ (cell12764 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12764 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12764 ⟨41,by decide⟩).lower ∧ (cell12764 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12764 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12764 ⟨42,by decide⟩).lower ∧ (cell12764 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12764 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12764 ⟨43,by decide⟩).lower ∧ (cell12764 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12764 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12764 ⟨44,by decide⟩).lower ∧ (cell12764 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12764 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12764 ⟨45,by decide⟩).lower ∧ (cell12764 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12764 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12764 ⟨46,by decide⟩).lower ∧ (cell12764 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12764 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12764 ⟨47,by decide⟩).lower ∧ (cell12764 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12764 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12764 ⟨48,by decide⟩).lower ∧ (cell12764 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12764 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12764 ⟨49,by decide⟩).lower ∧ (cell12764 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12764 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12764 ⟨50,by decide⟩).lower ∧ (cell12764 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12764 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12764 ⟨51,by decide⟩).lower ∧ (cell12764 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12764 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12764 ⟨52,by decide⟩).lower ∧ (cell12764 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12764 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12764 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12764 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12764,cell12764,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12764 i).lower ∧
    (cell12764 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12764 i).upper ≤ (0.532 : ℝ) ∧
    (cell12764 i).centre ≤ (0.1 : ℝ) ∧ (cell12764 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12764 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12764 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12764

/-! The local source numeric instances at 12764 have no network premises. -/
namespace BstLean.Part269.N12764
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12764)
open BstLean.Part268 (cell12764)

noncomputable def sourceNumerics12764 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12764 (cell12764 i)
      scalarRow12764.M scalarRow12764.H scalarRow12764.xi := by
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
    energy_allowance := scalarRow12764.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12764]
    centre_nonneg := (scalarRow12764.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12764])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12764
/-! Actual 12765 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12765 ≤ (1.035717132628 : ℝ) := by
  have hr : (112.982299498638 : ℝ) ≤ √(12765 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.982299498638 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12765 12765 (11 / 1000) ≤
    (0.008460502350 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12765) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.982299498638 : ℝ) ≤ √(12765 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12765)
  have hdiv : K / √(12765 : ℝ) ≤ K / 112.982299498638 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.982299498638 ≤ (0.008460502350 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12765.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12765 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12765 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12765 := gPlus_lower 12765
end BstLean.Part269.N12765

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12765
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035717132627 : ℝ) ≤ wn 12765 := by
  have hn : √(12765 : ℝ) ≤ 112.982299498639 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12765 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.982299498639 ≤ 2 / √(12765 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250576000 : ℝ) ≤ rhoBar 12765 BstLean.Part154.csC ∧
    rhoBar 12765 BstLean.Part154.csC ≤ 0.000250576388 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035717132627 : ℝ) / (1.295212 * 12765) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035717132628 : ℝ) / (1.29521 * 12765) := by gcongr
      _ ≤ (0.000250576388 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12765 BstLean.Part154.csC) ≤ 0.001002368341 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12765 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) ≤ 0.000191391889 ∧
    cc1 (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) ≤ 0.000121783940 ∧
    cc2 (rhoBar 12765 BstLean.Part154.csC) ≤ 0.000070696522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12765 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12765 BstLean.Part154.csC * nuR (rhoBar 12765 BstLean.Part154.csC)) ≤ 0.000501168474 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250576388 : ℝ) * 0.001002368341 := by gcongr
      _ ≤ (0.000501168474 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12765 BstLean.Part154.csC) * nuR (rhoBar 12765 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002368341 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12765 BstLean.Part154.csC) * rhoBar 12765 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250576388 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250576388 / 2 + 0.399 * 0.001002368341 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191391889 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501168474 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121783940 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250576388 / 1.414213562 := by gcongr
      _ ≤ (0.000070696522 : ℝ) := by norm_num

end BstLean.Part269.N12765

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12765
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) ≤ 1.58191E-7 := by
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12765 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12765 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191391889 : ℝ) ^ 2 + 0.000121783940 ^ 2 + 3 * 0.000070696522 ^ 2 +
        2 * 0.797885 * 0.000191391889 * 0.000121783940 + 2 * 0.000191391889 * 0.000070696522 +
        4 * 0.797885 * 0.000121783940 * 0.000070696522 := by gcongr
    _ ≤ (1.58191E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12765 BstLean.Part154.csC Θ ≤ 0.002615432108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12765 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12765 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035717132628 * 1.58191E-7 / (0.000250576000 : ℝ) := by gcongr
    _ ≤ 0.002615432108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12765 BstLean.Part154.csC Θ ≤ 0.002901707775 + 0.000660878327 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12765 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035717132628 : ℝ) * ((2 * Θ * 0.000250576388 +
        (6863 / 10000) * 0.000250576388 * 12765 * 0.001002368341) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002901707775 + 0.000660878327 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12765 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12765 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12765 0.011 Θ ∧ gammaRatio 12765 0.011 Θ ≤ 0.000086141683 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12765 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035717132628 : ℝ) * 0.525 / ((1 - 0.011) * 12765) := by gcongr
      _ ≤ (0.000086141683 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12765 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12765 0.011 Θ) :=
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
    badAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12765 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12765 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12765 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12765 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12765 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12765 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12765 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12765 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12765 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12765 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035717132628 : ℝ) * 12765 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003461869245 + 0.003276310435 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12765

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12765
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12765 BstLean.Part154.csC) (piBar (rhoBar 12765 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12765 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12765 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12765 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12765 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12765 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12765 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12765 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12765 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12765 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052349068795 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12765) ≤ 0.010570129891 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12765 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035717132628)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010570129891 + 2 * 0.737676 / 12765) := by gcongr
    _ ≤ (0.052349068795 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12765 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12765

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12765
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506492816 : ℝ) ≤ plow 12765 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12765) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688532224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373101857) : eMP 12765 0.011 xi bn ≤ 0.001182200946 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12765 : ℝ) * (1 - 0.011))) ≤ 0.000584544775 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373101857 / (12765 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584544775 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584544775 : ℝ) + 3.141593 * 0.052688532224 / (12765 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182200946 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688532224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373101857) : PiBarMP 12765 12 0.011 xi bn ≤ 0.160835776834 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12765 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037055389042 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.359178530282 : ℝ) ≤ √((12765 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.982299498638 : ℝ) ≤ √(12765 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12765) ≤ 0.123314964597 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037055389042 + 0.052688532224 * 1.772454 / (2 * (112.359178530282 : ℝ))) * (1 + 0.001182200946) +
        8 / (12765 * 112.982299498638) + 0.123314964597 := by gcongr
    _ ≤ (0.160835776834 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688532224)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373101857) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281888895893) :
    parallelOracle 12765 0.011 xi bn cd ≤ 0.161821127107 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12765 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12765 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506492816 : ℝ) ≤ plow 12765 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.982299498638 : ℝ) ≤ √(12765 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281888895893 : ℝ) / (2 * 0.560506492816 * 112.982299498638)) * 0.160835776834 +
        0.281888895893 ^ 2 / (2 * 0.560506492816 * 112.982299498638) := by gcongr
    _ ≤ (0.161821127107 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688532224) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373101857)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281888895893) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12765 12765 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506492816 : ℝ) ≤ plow 12765 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.982299498638 : ℝ) ≤ √(12765 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12765 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12765 Θ 1.22 ≤ 0.011737241196 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.982299498638 := by gcongr <;> linarith
      _ ≤ (0.011737241196 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12765 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12765 12765 0.011 ≤ 0.008460502350 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12765 12765 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12765 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12765 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12765 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12765 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161821127107 + 0.011737241196 + (0.008460502350 : ℝ) *
        (1 + 2 * (0.281888895893 + 0.011737241196) / (0.560506492816 * 112.982299498638))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12765]

end BstLean.Part269.N12765

/-! The original eight local profiles supply actual 12765 moment certificates. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12765 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052688532224 ∧
    0 ≤ bN 12765 BstLean.Part154.csC (groupTheta g) ∧ bN 12765 BstLean.Part154.csC (groupTheta g) ≤ 0.001373101857 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12765 12765 0.011
      (momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12765 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12765 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12765 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229539827098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12765 0.011
      (momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12765 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12765
/-! The actual computed-centre upper energy formula at 12765. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12765

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12765)
open BstLean.Part268 (cell12765)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085302937677
  | 2 => 0.086242295735
  | 3 => 0.087179306859
  | 4 => 0.088115276451
  | 5 => 0.089051787091
  | 6 => 0.089990740172
  | 7 => 0.090934401537
  | 8 => 0.091885451179
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12765 12765 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12765 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12765

/-! Actual upper energy certificates on all 43 source endpoints at 12765. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12765)
open BstLean.Part268 (cell12765)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12765 (gMinus 12765) (1 - (cell12765 i).lower) ≤ 1 ∧
    energyUpper 12765 (gMinus 12765) (BstLean.Part211.gPlus 12765)
      (finiteEnergy 12765 12765 0.011) (1 - (cell12765 i).lower) ≤
      (cell12765 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨10,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨11,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨12,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨13,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨14,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨15,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨16,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨17,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨18,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨19,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨20,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨21,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨22,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨23,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨24,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨25,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨26,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨27,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨28,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨29,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨30,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨31,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨32,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨33,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨34,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨35,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨36,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨37,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨38,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨39,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨40,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨41,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨42,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨43,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨44,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨45,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨46,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨47,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨48,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨49,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨50,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨51,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12765) (by norm_num)
        (q := 1 - (cell12765 ⟨52,by decide⟩).lower)
        (by norm_num [cell12765]) (by norm_num [cell12765])
      exact ⟨E.1,E.2.trans (by norm_num [cell12765])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12765

/-! Source-cell containment and simple scalar guards at 12765. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12765)
open BstLean.Part268 (cell12765)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12765 ⟨10,by decide⟩).lower ∧ (cell12765 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12765 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12765 ⟨11,by decide⟩).lower ∧ (cell12765 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12765 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12765 ⟨12,by decide⟩).lower ∧ (cell12765 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12765 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12765 ⟨13,by decide⟩).lower ∧ (cell12765 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12765 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12765 ⟨14,by decide⟩).lower ∧ (cell12765 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12765 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12765 ⟨15,by decide⟩).lower ∧ (cell12765 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12765 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12765 ⟨16,by decide⟩).lower ∧ (cell12765 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12765 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12765 ⟨17,by decide⟩).lower ∧ (cell12765 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12765 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12765 ⟨18,by decide⟩).lower ∧ (cell12765 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12765 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12765 ⟨19,by decide⟩).lower ∧ (cell12765 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12765 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12765 ⟨20,by decide⟩).lower ∧ (cell12765 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12765 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12765 ⟨21,by decide⟩).lower ∧ (cell12765 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12765 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12765 ⟨22,by decide⟩).lower ∧ (cell12765 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12765 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12765 ⟨23,by decide⟩).lower ∧ (cell12765 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12765 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12765 ⟨24,by decide⟩).lower ∧ (cell12765 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12765 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12765 ⟨25,by decide⟩).lower ∧ (cell12765 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12765 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12765 ⟨26,by decide⟩).lower ∧ (cell12765 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12765 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12765 ⟨27,by decide⟩).lower ∧ (cell12765 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12765 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12765 ⟨28,by decide⟩).lower ∧ (cell12765 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12765 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12765 ⟨29,by decide⟩).lower ∧ (cell12765 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12765 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12765 ⟨30,by decide⟩).lower ∧ (cell12765 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12765 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12765 ⟨31,by decide⟩).lower ∧ (cell12765 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12765 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12765 ⟨32,by decide⟩).lower ∧ (cell12765 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12765 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12765 ⟨33,by decide⟩).lower ∧ (cell12765 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12765 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12765 ⟨34,by decide⟩).lower ∧ (cell12765 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12765 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12765 ⟨35,by decide⟩).lower ∧ (cell12765 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12765 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12765 ⟨36,by decide⟩).lower ∧ (cell12765 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12765 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12765 ⟨37,by decide⟩).lower ∧ (cell12765 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12765 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12765 ⟨38,by decide⟩).lower ∧ (cell12765 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12765 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12765 ⟨39,by decide⟩).lower ∧ (cell12765 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12765 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12765 ⟨40,by decide⟩).lower ∧ (cell12765 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12765 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12765 ⟨41,by decide⟩).lower ∧ (cell12765 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12765 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12765 ⟨42,by decide⟩).lower ∧ (cell12765 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12765 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12765 ⟨43,by decide⟩).lower ∧ (cell12765 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12765 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12765 ⟨44,by decide⟩).lower ∧ (cell12765 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12765 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12765 ⟨45,by decide⟩).lower ∧ (cell12765 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12765 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12765 ⟨46,by decide⟩).lower ∧ (cell12765 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12765 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12765 ⟨47,by decide⟩).lower ∧ (cell12765 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12765 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12765 ⟨48,by decide⟩).lower ∧ (cell12765 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12765 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12765 ⟨49,by decide⟩).lower ∧ (cell12765 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12765 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12765 ⟨50,by decide⟩).lower ∧ (cell12765 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12765 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12765 ⟨51,by decide⟩).lower ∧ (cell12765 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12765 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12765 ⟨52,by decide⟩).lower ∧ (cell12765 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12765 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12765 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12765 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12765,cell12765,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12765 i).lower ∧
    (cell12765 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12765 i).upper ≤ (0.532 : ℝ) ∧
    (cell12765 i).centre ≤ (0.1 : ℝ) ∧ (cell12765 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12765 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12765 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12765

/-! The local source numeric instances at 12765 have no network premises. -/
namespace BstLean.Part269.N12765
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12765)
open BstLean.Part268 (cell12765)

noncomputable def sourceNumerics12765 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12765 (cell12765 i)
      scalarRow12765.M scalarRow12765.H scalarRow12765.xi := by
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
    energy_allowance := scalarRow12765.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12765]
    centre_nonneg := (scalarRow12765.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12765])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12765
/-! Actual 12766 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12766 ≤ (1.035715721412 : ℝ) := by
  have hr : (112.986724883943 : ℝ) ≤ √(12766 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.986724883943 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12766 12766 (11 / 1000) ≤
    (0.008460170972 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12766) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.986724883943 : ℝ) ≤ √(12766 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12766)
  have hdiv : K / √(12766 : ℝ) ≤ K / 112.986724883943 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.986724883943 ≤ (0.008460170972 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12766.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12766 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12766 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12766 := gPlus_lower 12766
end BstLean.Part269.N12766

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12766
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035715721411 : ℝ) ≤ wn 12766 := by
  have hn : √(12766 : ℝ) ≤ 112.986724883944 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12766 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.986724883944 ≤ 2 / √(12766 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250556030 : ℝ) ≤ rhoBar 12766 BstLean.Part154.csC ∧
    rhoBar 12766 BstLean.Part154.csC ≤ 0.000250556418 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035715721411 : ℝ) / (1.295212 * 12766) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035715721412 : ℝ) / (1.29521 * 12766) := by gcongr
      _ ≤ (0.000250556418 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12766 BstLean.Part154.csC) ≤ 0.001002288451 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12766 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) ≤ 0.000191376636 ∧
    cc1 (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) ≤ 0.000121774234 ∧
    cc2 (rhoBar 12766 BstLean.Part154.csC) ≤ 0.000070690887 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12766 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12766 BstLean.Part154.csC * nuR (rhoBar 12766 BstLean.Part154.csC)) ≤ 0.000501128531 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250556418 : ℝ) * 0.001002288451 := by gcongr
      _ ≤ (0.000501128531 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12766 BstLean.Part154.csC) * nuR (rhoBar 12766 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002288451 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12766 BstLean.Part154.csC) * rhoBar 12766 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250556418 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250556418 / 2 + 0.399 * 0.001002288451 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191376636 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501128531 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121774234 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250556418 / 1.414213562 := by gcongr
      _ ≤ (0.000070690887 : ℝ) := by norm_num

end BstLean.Part269.N12766

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12766
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) ≤ 1.58166E-7 := by
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12766 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12766 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191376636 : ℝ) ^ 2 + 0.000121774234 ^ 2 + 3 * 0.000070690887 ^ 2 +
        2 * 0.797885 * 0.000191376636 * 0.000121774234 + 2 * 0.000191376636 * 0.000070690887 +
        4 * 0.797885 * 0.000121774234 * 0.000070690887 := by gcongr
    _ ≤ (1.58166E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12766 BstLean.Part154.csC Θ ≤ 0.002615223634 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12766 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12766 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035715721412 * 1.58166E-7 / (0.000250556030 : ℝ) := by gcongr
    _ ≤ 0.002615223634 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12766 BstLean.Part154.csC Θ ≤ 0.002901468597 + 0.000660824757 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12766 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035715721412 : ℝ) * ((2 * Θ * 0.000250556418 +
        (6863 / 10000) * 0.000250556418 * 12766 * 0.001002288451) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002901468597 + 0.000660824757 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12766 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12766 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12766 0.011 Θ ∧ gammaRatio 12766 0.011 Θ ≤ 0.000086134818 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12766 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035715721412 : ℝ) * 0.525 / ((1 - 0.011) * 12766) := by gcongr
      _ ≤ (0.000086134818 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12766 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12766 0.011 Θ) :=
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
    badAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12766 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12766 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12766 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12766 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12766 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12766 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12766 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12766 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12766 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12766 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035715721412 : ℝ) * 12766 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003461630067 + 0.003276048391 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12766

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12766
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12766 BstLean.Part154.csC) (piBar (rhoBar 12766 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12766 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12766 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12766 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12766 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12766 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12766 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12766 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12766 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12766 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052346996250 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12766) ≤ 0.010569715888 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12766 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035715721412)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010569715888 + 2 * 0.737676 / 12766) := by gcongr
    _ ≤ (0.052346996250 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12766 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12766

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12766
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506537576 : ℝ) ≤ plow 12766 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12766) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688155473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372992408) : eMP 12766 0.011 xi bn ≤ 0.001182107441 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12766 : ℝ) * (1 - 0.011))) ≤ 0.000584498583 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372992408 / (12766 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584498583 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584498583 : ℝ) + 3.141593 * 0.052688155473 / (12766 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182107441 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688155473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372992408) : PiBarMP 12766 12 0.011 xi bn ≤ 0.160829444889 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12766 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037053912183 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.363579508664 : ℝ) ≤ √((12766 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.986724883943 : ℝ) ≤ √(12766 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12766) ≤ 0.123310134683 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037053912183 + 0.052688155473 * 1.772454 / (2 * (112.363579508664 : ℝ))) * (1 + 0.001182107441) +
        8 / (12766 * 112.986724883943) + 0.123310134683 := by gcongr
    _ ≤ (0.160829444889 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688155473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372992408) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281886002681) :
    parallelOracle 12766 0.011 xi bn cd ≤ 0.161814725846 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12766 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12766 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506537576 : ℝ) ≤ plow 12766 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.986724883943 : ℝ) ≤ √(12766 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281886002681 : ℝ) / (2 * 0.560506537576 * 112.986724883943)) * 0.160829444889 +
        0.281886002681 ^ 2 / (2 * 0.560506537576 * 112.986724883943) := by gcongr
    _ ≤ (0.161814725846 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052688155473) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372992408)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281886002681) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12766 12766 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506537576 : ℝ) ≤ plow 12766 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.986724883943 : ℝ) ≤ √(12766 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12766 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12766 Θ 1.22 ≤ 0.011736781480 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.986724883943 := by gcongr <;> linarith
      _ ≤ (0.011736781480 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12766 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12766 12766 0.011 ≤ 0.008460170972 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12766 12766 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12766 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12766 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12766 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12766 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161814725846 + 0.011736781480 + (0.008460170972 : ℝ) *
        (1 + 2 * (0.281886002681 + 0.011736781480) / (0.560506537576 * 112.986724883943))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12766]

end BstLean.Part269.N12766

/-! The original eight local profiles supply actual 12766 moment certificates. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12766 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052688155473 ∧
    0 ≤ bN 12766 BstLean.Part154.csC (groupTheta g) ∧ bN 12766 BstLean.Part154.csC (groupTheta g) ≤ 0.001372992408 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12766 12766 0.011
      (momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12766 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12766 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12766 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229539006431 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12766 0.011
      (momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12766 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12766
/-! The actual computed-centre upper energy formula at 12766. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12766

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12766)
open BstLean.Part268 (cell12766)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085300090090
  | 2 => 0.086239397364
  | 3 => 0.087176350544
  | 4 => 0.088112253366
  | 5 => 0.089048686447
  | 6 => 0.089987548882
  | 7 => 0.090931103840
  | 8 => 0.091882028226
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12766 12766 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12766 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12766

/-! Actual upper energy certificates on all 43 source endpoints at 12766. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12766)
open BstLean.Part268 (cell12766)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12766 (gMinus 12766) (1 - (cell12766 i).lower) ≤ 1 ∧
    energyUpper 12766 (gMinus 12766) (BstLean.Part211.gPlus 12766)
      (finiteEnergy 12766 12766 0.011) (1 - (cell12766 i).lower) ≤
      (cell12766 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨10,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨11,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨12,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨13,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨14,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨15,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨16,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨17,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨18,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨19,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨20,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨21,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨22,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨23,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨24,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨25,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨26,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨27,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨28,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨29,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨30,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨31,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨32,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨33,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨34,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨35,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨36,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨37,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨38,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨39,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨40,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨41,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨42,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨43,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨44,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨45,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨46,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨47,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨48,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨49,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨50,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨51,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12766) (by norm_num)
        (q := 1 - (cell12766 ⟨52,by decide⟩).lower)
        (by norm_num [cell12766]) (by norm_num [cell12766])
      exact ⟨E.1,E.2.trans (by norm_num [cell12766])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12766

/-! Source-cell containment and simple scalar guards at 12766. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12766)
open BstLean.Part268 (cell12766)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12766 ⟨10,by decide⟩).lower ∧ (cell12766 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12766 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12766 ⟨11,by decide⟩).lower ∧ (cell12766 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12766 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12766 ⟨12,by decide⟩).lower ∧ (cell12766 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12766 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12766 ⟨13,by decide⟩).lower ∧ (cell12766 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12766 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12766 ⟨14,by decide⟩).lower ∧ (cell12766 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12766 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12766 ⟨15,by decide⟩).lower ∧ (cell12766 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12766 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12766 ⟨16,by decide⟩).lower ∧ (cell12766 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12766 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12766 ⟨17,by decide⟩).lower ∧ (cell12766 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12766 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12766 ⟨18,by decide⟩).lower ∧ (cell12766 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12766 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12766 ⟨19,by decide⟩).lower ∧ (cell12766 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12766 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12766 ⟨20,by decide⟩).lower ∧ (cell12766 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12766 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12766 ⟨21,by decide⟩).lower ∧ (cell12766 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12766 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12766 ⟨22,by decide⟩).lower ∧ (cell12766 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12766 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12766 ⟨23,by decide⟩).lower ∧ (cell12766 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12766 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12766 ⟨24,by decide⟩).lower ∧ (cell12766 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12766 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12766 ⟨25,by decide⟩).lower ∧ (cell12766 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12766 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12766 ⟨26,by decide⟩).lower ∧ (cell12766 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12766 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12766 ⟨27,by decide⟩).lower ∧ (cell12766 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12766 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12766 ⟨28,by decide⟩).lower ∧ (cell12766 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12766 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12766 ⟨29,by decide⟩).lower ∧ (cell12766 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12766 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12766 ⟨30,by decide⟩).lower ∧ (cell12766 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12766 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12766 ⟨31,by decide⟩).lower ∧ (cell12766 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12766 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12766 ⟨32,by decide⟩).lower ∧ (cell12766 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12766 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12766 ⟨33,by decide⟩).lower ∧ (cell12766 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12766 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12766 ⟨34,by decide⟩).lower ∧ (cell12766 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12766 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12766 ⟨35,by decide⟩).lower ∧ (cell12766 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12766 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12766 ⟨36,by decide⟩).lower ∧ (cell12766 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12766 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12766 ⟨37,by decide⟩).lower ∧ (cell12766 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12766 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12766 ⟨38,by decide⟩).lower ∧ (cell12766 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12766 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12766 ⟨39,by decide⟩).lower ∧ (cell12766 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12766 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12766 ⟨40,by decide⟩).lower ∧ (cell12766 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12766 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12766 ⟨41,by decide⟩).lower ∧ (cell12766 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12766 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12766 ⟨42,by decide⟩).lower ∧ (cell12766 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12766 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12766 ⟨43,by decide⟩).lower ∧ (cell12766 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12766 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12766 ⟨44,by decide⟩).lower ∧ (cell12766 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12766 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12766 ⟨45,by decide⟩).lower ∧ (cell12766 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12766 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12766 ⟨46,by decide⟩).lower ∧ (cell12766 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12766 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12766 ⟨47,by decide⟩).lower ∧ (cell12766 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12766 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12766 ⟨48,by decide⟩).lower ∧ (cell12766 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12766 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12766 ⟨49,by decide⟩).lower ∧ (cell12766 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12766 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12766 ⟨50,by decide⟩).lower ∧ (cell12766 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12766 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12766 ⟨51,by decide⟩).lower ∧ (cell12766 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12766 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12766 ⟨52,by decide⟩).lower ∧ (cell12766 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12766 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12766 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12766 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12766,cell12766,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12766 i).lower ∧
    (cell12766 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12766 i).upper ≤ (0.532 : ℝ) ∧
    (cell12766 i).centre ≤ (0.1 : ℝ) ∧ (cell12766 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12766 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12766 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12766

/-! The local source numeric instances at 12766 have no network premises. -/
namespace BstLean.Part269.N12766
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12766)
open BstLean.Part268 (cell12766)

noncomputable def sourceNumerics12766 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12766 (cell12766 i)
      scalarRow12766.M scalarRow12766.H scalarRow12766.xi := by
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
    energy_allowance := scalarRow12766.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12766]
    centre_nonneg := (scalarRow12766.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12766])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12766
/-! Actual 12767 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12767 ≤ (1.035714310362 : ℝ) := by
  have hr : (112.991150095925 : ℝ) ≤ √(12767 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.991150095925 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12767 12767 (11 / 1000) ≤
    (0.008459839634 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12767) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.991150095925 : ℝ) ≤ √(12767 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12767)
  have hdiv : K / √(12767 : ℝ) ≤ K / 112.991150095925 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.991150095925 ≤ (0.008459839634 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12767.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12767 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12767 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12767 := gPlus_lower 12767
end BstLean.Part269.N12767

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12767
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035714310361 : ℝ) ≤ wn 12767 := by
  have hn : √(12767 : ℝ) ≤ 112.991150095926 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12767 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.991150095926 ≤ 2 / √(12767 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250536064 : ℝ) ≤ rhoBar 12767 BstLean.Part154.csC ∧
    rhoBar 12767 BstLean.Part154.csC ≤ 0.000250536451 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035714310361 : ℝ) / (1.295212 * 12767) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035714310362 : ℝ) / (1.29521 * 12767) := by gcongr
      _ ≤ (0.000250536451 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12767 BstLean.Part154.csC) ≤ 0.001002208573 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12767 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) ≤ 0.000191361384 ∧
    cc1 (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) ≤ 0.000121764529 ∧
    cc2 (rhoBar 12767 BstLean.Part154.csC) ≤ 0.000070685254 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12767 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12767 BstLean.Part154.csC * nuR (rhoBar 12767 BstLean.Part154.csC)) ≤ 0.000501088595 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250536451 : ℝ) * 0.001002208573 := by gcongr
      _ ≤ (0.000501088595 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12767 BstLean.Part154.csC) * nuR (rhoBar 12767 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002208573 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12767 BstLean.Part154.csC) * rhoBar 12767 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250536451 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250536451 / 2 + 0.399 * 0.001002208573 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191361384 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501088595 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121764529 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250536451 / 1.414213562 := by gcongr
      _ ≤ (0.000070685254 : ℝ) := by norm_num

end BstLean.Part269.N12767

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12767
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) ≤ 1.58141E-7 := by
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12767 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12767 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191361384 : ℝ) ^ 2 + 0.000121764529 ^ 2 + 3 * 0.000070685254 ^ 2 +
        2 * 0.797885 * 0.000191361384 * 0.000121764529 + 2 * 0.000191361384 * 0.000070685254 +
        4 * 0.797885 * 0.000121764529 * 0.000070685254 := by gcongr
    _ ≤ (1.58141E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12767 BstLean.Part154.csC Θ ≤ 0.002615015087 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12767 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12767 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035714310362 * 1.58141E-7 / (0.000250536064 : ℝ) := by gcongr
    _ ≤ 0.002615015087 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12767 BstLean.Part154.csC Θ ≤ 0.002901229453 + 0.000660771196 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12767 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035714310362 : ℝ) * ((2 * Θ * 0.000250536451 +
        (6863 / 10000) * 0.000250536451 * 12767 * 0.001002208573) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002901229453 + 0.000660771196 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12767 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12767 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12767 0.011 Θ ∧ gammaRatio 12767 0.011 Θ ≤ 0.000086127954 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12767 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035714310362 : ℝ) * 0.525 / ((1 - 0.011) * 12767) := by gcongr
      _ ≤ (0.000086127954 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12767 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12767 0.011 Θ) :=
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
    badAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12767 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12767 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12767 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12767 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12767 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12767 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12767 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12767 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12767 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12767 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035714310362 : ℝ) * 12767 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003461390923 + 0.003275786283 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12767

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12767
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12767 BstLean.Part154.csC) (piBar (rhoBar 12767 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12767 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12767 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12767 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12767 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12767 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12767 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12767 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12767 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12767 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052344923946 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12767) ≤ 0.010569301933 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12767 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035714310362)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010569301933 + 2 * 0.737676 / 12767) := by gcongr
    _ ≤ (0.052344923946 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12767 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12767

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12767
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506582329 : ℝ) ≤ plow 12767 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12767) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687778722)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372882921) : eMP 12767 0.011 xi bn ≤ 0.001182013928 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12767 : ℝ) * (1 - 0.011))) ≤ 0.000584452387 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372882921 / (12767 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584452387 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584452387 : ℝ) + 3.141593 * 0.052687778722 / (12767 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182013928 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687778722)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372882921) : PiBarMP 12767 12 0.011 xi bn ≤ 0.160823112940 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12767 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037052434752 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.367980314678 : ℝ) ≤ √((12767 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.991150095925 : ℝ) ≤ √(12767 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12767) ≤ 0.123305305336 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037052434752 + 0.052687778722 * 1.772454 / (2 * (112.367980314678 : ℝ))) * (1 + 0.001182013928) +
        8 / (12767 * 112.991150095925) + 0.123305305336 := by gcongr
    _ ≤ (0.160823112940 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687778722)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372882921) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281883109707) :
    parallelOracle 12767 0.011 xi bn cd ≤ 0.161808324590 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12767 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12767 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506582329 : ℝ) ≤ plow 12767 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.991150095925 : ℝ) ≤ √(12767 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281883109707 : ℝ) / (2 * 0.560506582329 * 112.991150095925)) * 0.160823112940 +
        0.281883109707 ^ 2 / (2 * 0.560506582329 * 112.991150095925) := by gcongr
    _ ≤ (0.161808324590 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687778722) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372882921)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281883109707) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12767 12767 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506582329 : ℝ) ≤ plow 12767 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.991150095925 : ℝ) ≤ √(12767 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12767 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12767 Θ 1.22 ≤ 0.011736321818 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.991150095925 := by gcongr <;> linarith
      _ ≤ (0.011736321818 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12767 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12767 12767 0.011 ≤ 0.008459839634 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12767 12767 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12767 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12767 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12767 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12767 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161808324590 + 0.011736321818 + (0.008459839634 : ℝ) *
        (1 + 2 * (0.281883109707 + 0.011736321818) / (0.560506582329 * 112.991150095925))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12767]

end BstLean.Part269.N12767

/-! The original eight local profiles supply actual 12767 moment certificates. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12767 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052687778722 ∧
    0 ≤ bN 12767 BstLean.Part154.csC (groupTheta g) ∧ bN 12767 BstLean.Part154.csC (groupTheta g) ≤ 0.001372882921 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12767 12767 0.011
      (momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12767 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12767 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12767 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229538185761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12767 0.011
      (momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12767 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12767
/-! The actual computed-centre upper energy formula at 12767. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12767

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12767)
open BstLean.Part268 (cell12767)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085297243518
  | 2 => 0.086236500048
  | 3 => 0.087173395334
  | 4 => 0.088109231449
  | 5 => 0.089045587047
  | 6 => 0.089984358927
  | 7 => 0.090927807590
  | 8 => 0.091878606856
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12767 12767 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12767 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12767

/-! Actual upper energy certificates on all 43 source endpoints at 12767. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12767)
open BstLean.Part268 (cell12767)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12767 (gMinus 12767) (1 - (cell12767 i).lower) ≤ 1 ∧
    energyUpper 12767 (gMinus 12767) (BstLean.Part211.gPlus 12767)
      (finiteEnergy 12767 12767 0.011) (1 - (cell12767 i).lower) ≤
      (cell12767 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨10,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨11,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨12,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨13,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨14,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨15,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨16,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨17,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨18,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨19,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨20,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨21,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨22,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨23,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨24,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨25,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨26,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨27,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨28,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨29,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨30,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨31,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨32,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨33,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨34,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨35,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨36,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨37,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨38,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨39,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨40,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨41,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨42,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨43,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨44,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨45,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨46,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨47,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨48,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨49,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨50,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨51,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12767) (by norm_num)
        (q := 1 - (cell12767 ⟨52,by decide⟩).lower)
        (by norm_num [cell12767]) (by norm_num [cell12767])
      exact ⟨E.1,E.2.trans (by norm_num [cell12767])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12767

/-! Source-cell containment and simple scalar guards at 12767. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12767)
open BstLean.Part268 (cell12767)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12767 ⟨10,by decide⟩).lower ∧ (cell12767 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12767 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12767 ⟨11,by decide⟩).lower ∧ (cell12767 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12767 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12767 ⟨12,by decide⟩).lower ∧ (cell12767 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12767 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12767 ⟨13,by decide⟩).lower ∧ (cell12767 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12767 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12767 ⟨14,by decide⟩).lower ∧ (cell12767 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12767 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12767 ⟨15,by decide⟩).lower ∧ (cell12767 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12767 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12767 ⟨16,by decide⟩).lower ∧ (cell12767 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12767 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12767 ⟨17,by decide⟩).lower ∧ (cell12767 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12767 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12767 ⟨18,by decide⟩).lower ∧ (cell12767 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12767 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12767 ⟨19,by decide⟩).lower ∧ (cell12767 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12767 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12767 ⟨20,by decide⟩).lower ∧ (cell12767 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12767 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12767 ⟨21,by decide⟩).lower ∧ (cell12767 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12767 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12767 ⟨22,by decide⟩).lower ∧ (cell12767 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12767 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12767 ⟨23,by decide⟩).lower ∧ (cell12767 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12767 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12767 ⟨24,by decide⟩).lower ∧ (cell12767 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12767 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12767 ⟨25,by decide⟩).lower ∧ (cell12767 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12767 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12767 ⟨26,by decide⟩).lower ∧ (cell12767 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12767 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12767 ⟨27,by decide⟩).lower ∧ (cell12767 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12767 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12767 ⟨28,by decide⟩).lower ∧ (cell12767 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12767 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12767 ⟨29,by decide⟩).lower ∧ (cell12767 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12767 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12767 ⟨30,by decide⟩).lower ∧ (cell12767 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12767 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12767 ⟨31,by decide⟩).lower ∧ (cell12767 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12767 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12767 ⟨32,by decide⟩).lower ∧ (cell12767 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12767 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12767 ⟨33,by decide⟩).lower ∧ (cell12767 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12767 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12767 ⟨34,by decide⟩).lower ∧ (cell12767 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12767 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12767 ⟨35,by decide⟩).lower ∧ (cell12767 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12767 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12767 ⟨36,by decide⟩).lower ∧ (cell12767 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12767 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12767 ⟨37,by decide⟩).lower ∧ (cell12767 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12767 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12767 ⟨38,by decide⟩).lower ∧ (cell12767 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12767 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12767 ⟨39,by decide⟩).lower ∧ (cell12767 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12767 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12767 ⟨40,by decide⟩).lower ∧ (cell12767 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12767 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12767 ⟨41,by decide⟩).lower ∧ (cell12767 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12767 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12767 ⟨42,by decide⟩).lower ∧ (cell12767 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12767 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12767 ⟨43,by decide⟩).lower ∧ (cell12767 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12767 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12767 ⟨44,by decide⟩).lower ∧ (cell12767 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12767 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12767 ⟨45,by decide⟩).lower ∧ (cell12767 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12767 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12767 ⟨46,by decide⟩).lower ∧ (cell12767 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12767 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12767 ⟨47,by decide⟩).lower ∧ (cell12767 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12767 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12767 ⟨48,by decide⟩).lower ∧ (cell12767 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12767 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12767 ⟨49,by decide⟩).lower ∧ (cell12767 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12767 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12767 ⟨50,by decide⟩).lower ∧ (cell12767 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12767 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12767 ⟨51,by decide⟩).lower ∧ (cell12767 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12767 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12767 ⟨52,by decide⟩).lower ∧ (cell12767 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12767 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12767 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12767 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12767,cell12767,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12767 i).lower ∧
    (cell12767 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12767 i).upper ≤ (0.532 : ℝ) ∧
    (cell12767 i).centre ≤ (0.1 : ℝ) ∧ (cell12767 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12767 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12767 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12767

/-! The local source numeric instances at 12767 have no network premises. -/
namespace BstLean.Part269.N12767
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12767)
open BstLean.Part268 (cell12767)

noncomputable def sourceNumerics12767 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12767 (cell12767 i)
      scalarRow12767.M scalarRow12767.H scalarRow12767.xi := by
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
    energy_allowance := scalarRow12767.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12767]
    centre_nonneg := (scalarRow12767.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12767])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12767
/-! Actual 12768 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12768 ≤ (1.035712899479 : ℝ) := by
  have hr : (112.995575134604 : ℝ) ≤ √(12768 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.995575134604 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12768 12768 (11 / 1000) ≤
    (0.008459508334 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12768) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.995575134604 : ℝ) ≤ √(12768 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12768)
  have hdiv : K / √(12768 : ℝ) ≤ K / 112.995575134604 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.995575134604 ≤ (0.008459508334 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12768.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12768 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12768 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12768 := gPlus_lower 12768
end BstLean.Part269.N12768

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12768
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035712899478 : ℝ) ≤ wn 12768 := by
  have hn : √(12768 : ℝ) ≤ 112.995575134605 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12768 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.995575134605 ≤ 2 / √(12768 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250516100 : ℝ) ≤ rhoBar 12768 BstLean.Part154.csC ∧
    rhoBar 12768 BstLean.Part154.csC ≤ 0.000250516488 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035712899478 : ℝ) / (1.295212 * 12768) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035712899479 : ℝ) / (1.29521 * 12768) := by gcongr
      _ ≤ (0.000250516488 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12768 BstLean.Part154.csC) ≤ 0.001002128711 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12768 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) ≤ 0.000191346135 ∧
    cc1 (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) ≤ 0.000121754826 ∧
    cc2 (rhoBar 12768 BstLean.Part154.csC) ≤ 0.000070679622 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12768 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12768 BstLean.Part154.csC * nuR (rhoBar 12768 BstLean.Part154.csC)) ≤ 0.000501048666 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250516488 : ℝ) * 0.001002128711 := by gcongr
      _ ≤ (0.000501048666 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12768 BstLean.Part154.csC) * nuR (rhoBar 12768 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002128711 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12768 BstLean.Part154.csC) * rhoBar 12768 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250516488 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250516488 / 2 + 0.399 * 0.001002128711 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191346135 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501048666 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121754826 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250516488 / 1.414213562 := by gcongr
      _ ≤ (0.000070679622 : ℝ) := by norm_num

end BstLean.Part269.N12768

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12768
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) ≤ 1.58116E-7 := by
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12768 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12768 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191346135 : ℝ) ^ 2 + 0.000121754826 ^ 2 + 3 * 0.000070679622 ^ 2 +
        2 * 0.797885 * 0.000191346135 * 0.000121754826 + 2 * 0.000191346135 * 0.000070679622 +
        4 * 0.797885 * 0.000121754826 * 0.000070679622 := by gcongr
    _ ≤ (1.58116E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12768 BstLean.Part154.csC Θ ≤ 0.002614806487 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12768 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12768 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035712899479 * 1.58116E-7 / (0.000250516100 : ℝ) := by gcongr
    _ ≤ 0.002614806487 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12768 BstLean.Part154.csC Θ ≤ 0.002900990368 + 0.000660717645 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12768 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035712899479 : ℝ) * ((2 * Θ * 0.000250516488 +
        (6863 / 10000) * 0.000250516488 * 12768 * 0.001002128711) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002900990368 + 0.000660717645 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12768 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12768 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12768 0.011 Θ ∧ gammaRatio 12768 0.011 Θ ≤ 0.000086121091 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12768 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035712899479 : ℝ) * 0.525 / ((1 - 0.011) * 12768) := by gcongr
      _ ≤ (0.000086121091 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12768 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12768 0.011 Θ) :=
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
    badAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12768 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12768 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12768 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12768 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12768 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12768 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12768 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12768 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12768 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12768 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035712899479 : ℝ) * 12768 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003461151838 + 0.003275524132 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12768

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12768
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12768 BstLean.Part154.csC) (piBar (rhoBar 12768 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12768 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12768 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12768 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12768 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12768 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12768 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12768 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12768 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12768 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052342851889 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12768) ≤ 0.010568888027 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12768 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035712899479)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010568888027 + 2 * 0.737676 / 12768) := by gcongr
    _ ≤ (0.052342851889 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12768 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12768

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12768
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506627075 : ℝ) ≤ plow 12768 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12768) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687402008)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372773406) : eMP 12768 0.011 xi bn ≤ 0.001181920412 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12768 : ℝ) * (1 - 0.011))) ≤ 0.000584406189 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372773406 / (12768 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584406189 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584406189 : ℝ) + 3.141593 * 0.052687402008 / (12768 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181920412 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687402008)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372773406) : PiBarMP 12768 12 0.011 xi bn ≤ 0.160816781123 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12768 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037050956884 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.372380948345 : ℝ) ≤ √((12768 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.995575134604 : ℝ) ≤ √(12768 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12768) ≤ 0.123300476556 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037050956884 + 0.052687402008 * 1.772454 / (2 * (112.372380948345 : ℝ))) * (1 + 0.001181920412) +
        8 / (12768 * 112.995575134604) + 0.123300476556 := by gcongr
    _ ≤ (0.160816781123 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687402008)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372773406) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281880217057) :
    parallelOracle 12768 0.011 xi bn cd ≤ 0.161801923475 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12768 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12768 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506627075 : ℝ) ≤ plow 12768 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.995575134604 : ℝ) ≤ √(12768 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281880217057 : ℝ) / (2 * 0.560506627075 * 112.995575134604)) * 0.160816781123 +
        0.281880217057 ^ 2 / (2 * 0.560506627075 * 112.995575134604) := by gcongr
    _ ≤ (0.161801923475 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687402008) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372773406)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281880217057) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12768 12768 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506627075 : ℝ) ≤ plow 12768 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.995575134604 : ℝ) ≤ √(12768 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12768 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12768 Θ 1.22 ≤ 0.011735862209 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.995575134604 := by gcongr <;> linarith
      _ ≤ (0.011735862209 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12768 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12768 12768 0.011 ≤ 0.008459508334 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12768 12768 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12768 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12768 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12768 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12768 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161801923475 + 0.011735862209 + (0.008459508334 : ℝ) *
        (1 + 2 * (0.281880217057 + 0.011735862209) / (0.560506627075 * 112.995575134604))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12768]

end BstLean.Part269.N12768

/-! The original eight local profiles supply actual 12768 moment certificates. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12768 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052687402008 ∧
    0 ≤ bN 12768 BstLean.Part154.csC (groupTheta g) ∧ bN 12768 BstLean.Part154.csC (groupTheta g) ≤ 0.001372773406 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12768 12768 0.011
      (momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12768 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12768 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12768 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229537365168 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12768 0.011
      (momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12768 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12768
/-! The actual computed-centre upper energy formula at 12768. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12768

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12768)
open BstLean.Part268 (cell12768)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085294397960
  | 2 => 0.086233603787
  | 3 => 0.087170441229
  | 4 => 0.088106210698
  | 5 => 0.089042488889
  | 6 => 0.089981170307
  | 7 => 0.090924512787
  | 8 => 0.091875187066
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12768 12768 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12768 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12768

/-! Actual upper energy certificates on all 43 source endpoints at 12768. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12768)
open BstLean.Part268 (cell12768)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12768 (gMinus 12768) (1 - (cell12768 i).lower) ≤ 1 ∧
    energyUpper 12768 (gMinus 12768) (BstLean.Part211.gPlus 12768)
      (finiteEnergy 12768 12768 0.011) (1 - (cell12768 i).lower) ≤
      (cell12768 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨10,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨11,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨12,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨13,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨14,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨15,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨16,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨17,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨18,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨19,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨20,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨21,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨22,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨23,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨24,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨25,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨26,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨27,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨28,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨29,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨30,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨31,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨32,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨33,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨34,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨35,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨36,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨37,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨38,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨39,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨40,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨41,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨42,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨43,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨44,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨45,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨46,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨47,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨48,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨49,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨50,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨51,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12768) (by norm_num)
        (q := 1 - (cell12768 ⟨52,by decide⟩).lower)
        (by norm_num [cell12768]) (by norm_num [cell12768])
      exact ⟨E.1,E.2.trans (by norm_num [cell12768])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12768

/-! Source-cell containment and simple scalar guards at 12768. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12768)
open BstLean.Part268 (cell12768)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12768 ⟨10,by decide⟩).lower ∧ (cell12768 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12768 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12768 ⟨11,by decide⟩).lower ∧ (cell12768 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12768 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12768 ⟨12,by decide⟩).lower ∧ (cell12768 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12768 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12768 ⟨13,by decide⟩).lower ∧ (cell12768 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12768 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12768 ⟨14,by decide⟩).lower ∧ (cell12768 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12768 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12768 ⟨15,by decide⟩).lower ∧ (cell12768 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12768 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12768 ⟨16,by decide⟩).lower ∧ (cell12768 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12768 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12768 ⟨17,by decide⟩).lower ∧ (cell12768 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12768 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12768 ⟨18,by decide⟩).lower ∧ (cell12768 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12768 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12768 ⟨19,by decide⟩).lower ∧ (cell12768 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12768 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12768 ⟨20,by decide⟩).lower ∧ (cell12768 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12768 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12768 ⟨21,by decide⟩).lower ∧ (cell12768 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12768 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12768 ⟨22,by decide⟩).lower ∧ (cell12768 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12768 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12768 ⟨23,by decide⟩).lower ∧ (cell12768 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12768 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12768 ⟨24,by decide⟩).lower ∧ (cell12768 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12768 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12768 ⟨25,by decide⟩).lower ∧ (cell12768 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12768 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12768 ⟨26,by decide⟩).lower ∧ (cell12768 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12768 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12768 ⟨27,by decide⟩).lower ∧ (cell12768 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12768 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12768 ⟨28,by decide⟩).lower ∧ (cell12768 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12768 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12768 ⟨29,by decide⟩).lower ∧ (cell12768 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12768 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12768 ⟨30,by decide⟩).lower ∧ (cell12768 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12768 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12768 ⟨31,by decide⟩).lower ∧ (cell12768 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12768 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12768 ⟨32,by decide⟩).lower ∧ (cell12768 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12768 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12768 ⟨33,by decide⟩).lower ∧ (cell12768 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12768 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12768 ⟨34,by decide⟩).lower ∧ (cell12768 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12768 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12768 ⟨35,by decide⟩).lower ∧ (cell12768 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12768 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12768 ⟨36,by decide⟩).lower ∧ (cell12768 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12768 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12768 ⟨37,by decide⟩).lower ∧ (cell12768 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12768 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12768 ⟨38,by decide⟩).lower ∧ (cell12768 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12768 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12768 ⟨39,by decide⟩).lower ∧ (cell12768 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12768 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12768 ⟨40,by decide⟩).lower ∧ (cell12768 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12768 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12768 ⟨41,by decide⟩).lower ∧ (cell12768 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12768 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12768 ⟨42,by decide⟩).lower ∧ (cell12768 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12768 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12768 ⟨43,by decide⟩).lower ∧ (cell12768 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12768 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12768 ⟨44,by decide⟩).lower ∧ (cell12768 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12768 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12768 ⟨45,by decide⟩).lower ∧ (cell12768 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12768 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12768 ⟨46,by decide⟩).lower ∧ (cell12768 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12768 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12768 ⟨47,by decide⟩).lower ∧ (cell12768 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12768 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12768 ⟨48,by decide⟩).lower ∧ (cell12768 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12768 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12768 ⟨49,by decide⟩).lower ∧ (cell12768 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12768 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12768 ⟨50,by decide⟩).lower ∧ (cell12768 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12768 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12768 ⟨51,by decide⟩).lower ∧ (cell12768 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12768 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12768 ⟨52,by decide⟩).lower ∧ (cell12768 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12768 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12768 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12768 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12768,cell12768,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12768 i).lower ∧
    (cell12768 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12768 i).upper ≤ (0.532 : ℝ) ∧
    (cell12768 i).centre ≤ (0.1 : ℝ) ∧ (cell12768 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12768 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12768 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12768

/-! The local source numeric instances at 12768 have no network premises. -/
namespace BstLean.Part269.N12768
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12768)
open BstLean.Part268 (cell12768)

noncomputable def sourceNumerics12768 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12768 (cell12768 i)
      scalarRow12768.M scalarRow12768.H scalarRow12768.xi := by
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
    energy_allowance := scalarRow12768.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12768]
    centre_nonneg := (scalarRow12768.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12768])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12768
/-! Actual 12769 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12769 ≤ (1.035711488762 : ℝ) := by
  have hr : (113.000000000000 : ℝ) ≤ √(12769 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.000000000000 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12769 12769 (11 / 1000) ≤
    (0.008459177073 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12769) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.000000000000 : ℝ) ≤ √(12769 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12769)
  have hdiv : K / √(12769 : ℝ) ≤ K / 113.000000000000 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.000000000000 ≤ (0.008459177073 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12769.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12769 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12769 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12769 := gPlus_lower 12769
end BstLean.Part269.N12769

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12769
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035711488761 : ℝ) ≤ wn 12769 := by
  have hn : √(12769 : ℝ) ≤ 113.000000000000 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12769 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.000000000000 ≤ 2 / √(12769 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250496140 : ℝ) ≤ rhoBar 12769 BstLean.Part154.csC ∧
    rhoBar 12769 BstLean.Part154.csC ≤ 0.000250496528 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035711488761 : ℝ) / (1.295212 * 12769) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035711488762 : ℝ) / (1.29521 * 12769) := by gcongr
      _ ≤ (0.000250496528 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12769 BstLean.Part154.csC) ≤ 0.001002048861 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12769 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) ≤ 0.000191330889 ∧
    cc1 (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) ≤ 0.000121745125 ∧
    cc2 (rhoBar 12769 BstLean.Part154.csC) ≤ 0.000070673990 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12769 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12769 BstLean.Part154.csC * nuR (rhoBar 12769 BstLean.Part154.csC)) ≤ 0.000501008744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250496528 : ℝ) * 0.001002048861 := by gcongr
      _ ≤ (0.000501008744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12769 BstLean.Part154.csC) * nuR (rhoBar 12769 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002048861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12769 BstLean.Part154.csC) * rhoBar 12769 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250496528 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250496528 / 2 + 0.399 * 0.001002048861 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191330889 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501008744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121745125 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250496528 / 1.414213562 := by gcongr
      _ ≤ (0.000070673990 : ℝ) := by norm_num

end BstLean.Part269.N12769

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12769
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) ≤ 1.58090E-7 := by
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12769 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12769 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191330889 : ℝ) ^ 2 + 0.000121745125 ^ 2 + 3 * 0.000070673990 ^ 2 +
        2 * 0.797885 * 0.000191330889 * 0.000121745125 + 2 * 0.000191330889 * 0.000070673990 +
        4 * 0.797885 * 0.000121745125 * 0.000070673990 := by gcongr
    _ ≤ (1.58090E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12769 BstLean.Part154.csC Θ ≤ 0.002614581275 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12769 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12769 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035711488762 * 1.58090E-7 / (0.000250496140 : ℝ) := by gcongr
    _ ≤ 0.002614581275 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12769 BstLean.Part154.csC Θ ≤ 0.002900751317 + 0.000660664102 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12769 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035711488762 : ℝ) * ((2 * Θ * 0.000250496528 +
        (6863 / 10000) * 0.000250496528 * 12769 * 0.001002048861) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002900751317 + 0.000660664102 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12769 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12769 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12769 0.011 Θ ∧ gammaRatio 12769 0.011 Θ ≤ 0.000086114229 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12769 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035711488762 : ℝ) * 0.525 / ((1 - 0.011) * 12769) := by gcongr
      _ ≤ (0.000086114229 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12769 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12769 0.011 Θ) :=
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
    badAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12769 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12769 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12769 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12769 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12769 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12769 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12769 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12769 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12769 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12769 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035711488762 : ℝ) * 12769 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003460912787 + 0.003275245377 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12769

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12769
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12769 BstLean.Part154.csC) (piBar (rhoBar 12769 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12769 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12769 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12769 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12769 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12769 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12769 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12769 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12769 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12769 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052340780075 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12769) ≤ 0.010568474169 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12769 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035711488762)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010568474169 + 2 * 0.737676 / 12769) := by gcongr
    _ ≤ (0.052340780075 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12769 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12769

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12769
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506671814 : ℝ) ≤ plow 12769 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12769) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687016610)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372655170) : eMP 12769 0.011 xi bn ≤ 0.001181823187 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12769 : ℝ) * (1 - 0.011))) ≤ 0.000584358138 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372655170 / (12769 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584358138 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584358138 : ℝ) + 3.141593 * 0.052687016610 / (12769 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181823187 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687016610)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372655170) : PiBarMP 12769 12 0.011 xi bn ≤ 0.160810331777 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12769 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037049361264 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.376781409684 : ℝ) ≤ √((12769 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.000000000000 : ℝ) ≤ √(12769 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12769) ≤ 0.123295648343 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037049361264 + 0.052687016610 * 1.772454 / (2 * (112.376781409684 : ℝ))) * (1 + 0.001181823187) +
        8 / (12769 * 113.000000000000) + 0.123295648343 := by gcongr
    _ ≤ (0.160810331777 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687016610)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372655170) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281877305731) :
    parallelOracle 12769 0.011 xi bn cd ≤ 0.161795404470 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12769 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12769 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506671814 : ℝ) ≤ plow 12769 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.000000000000 : ℝ) ≤ √(12769 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281877305731 : ℝ) / (2 * 0.560506671814 * 113.000000000000)) * 0.160810331777 +
        0.281877305731 ^ 2 / (2 * 0.560506671814 * 113.000000000000) := by gcongr
    _ ≤ (0.161795404470 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052687016610) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372655170)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281877305731) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12769 12769 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506671814 : ℝ) ≤ plow 12769 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.000000000000 : ℝ) ≤ √(12769 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12769 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12769 Θ 1.22 ≤ 0.011735402655 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.000000000000 := by gcongr <;> linarith
      _ ≤ (0.011735402655 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12769 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12769 12769 0.011 ≤ 0.008459177073 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12769 12769 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12769 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12769 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12769 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12769 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161795404470 + 0.011735402655 + (0.008459177073 : ℝ) *
        (1 + 2 * (0.281877305731 + 0.011735402655) / (0.560506671814 * 113.000000000000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12769]

end BstLean.Part269.N12769

/-! The original eight local profiles supply actual 12769 moment certificates. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12769 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052687016610 ∧
    0 ≤ bN 12769 BstLean.Part154.csC (groupTheta g) ∧ bN 12769 BstLean.Part154.csC (groupTheta g) ≤ 0.001372655170 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12769 12769 0.011
      (momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12769 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12769 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12769 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229536525656 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12769 0.011
      (momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12769 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12769
/-! The actual computed-centre upper energy formula at 12769. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12769

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12769)
open BstLean.Part268 (cell12769)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085291553413
  | 2 => 0.086230708578
  | 3 => 0.087167488228
  | 4 => 0.088103191113
  | 5 => 0.089039391973
  | 6 => 0.089977983021
  | 7 => 0.090921219429
  | 8 => 0.091871768856
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12769 12769 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12769 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12769

/-! Actual upper energy certificates on all 43 source endpoints at 12769. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12769)
open BstLean.Part268 (cell12769)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12769 (gMinus 12769) (1 - (cell12769 i).lower) ≤ 1 ∧
    energyUpper 12769 (gMinus 12769) (BstLean.Part211.gPlus 12769)
      (finiteEnergy 12769 12769 0.011) (1 - (cell12769 i).lower) ≤
      (cell12769 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨10,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨11,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨12,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨13,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨14,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨15,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨16,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨17,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨18,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨19,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨20,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨21,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨22,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨23,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨24,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨25,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨26,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨27,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨28,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨29,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨30,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨31,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨32,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨33,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨34,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨35,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨36,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨37,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨38,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨39,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨40,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨41,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨42,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨43,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨44,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨45,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨46,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨47,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨48,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨49,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨50,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨51,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12769) (by norm_num)
        (q := 1 - (cell12769 ⟨52,by decide⟩).lower)
        (by norm_num [cell12769]) (by norm_num [cell12769])
      exact ⟨E.1,E.2.trans (by norm_num [cell12769])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12769

/-! Source-cell containment and simple scalar guards at 12769. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12769)
open BstLean.Part268 (cell12769)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12769 ⟨10,by decide⟩).lower ∧ (cell12769 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12769 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12769 ⟨11,by decide⟩).lower ∧ (cell12769 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12769 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12769 ⟨12,by decide⟩).lower ∧ (cell12769 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12769 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12769 ⟨13,by decide⟩).lower ∧ (cell12769 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12769 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12769 ⟨14,by decide⟩).lower ∧ (cell12769 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12769 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12769 ⟨15,by decide⟩).lower ∧ (cell12769 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12769 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12769 ⟨16,by decide⟩).lower ∧ (cell12769 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12769 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12769 ⟨17,by decide⟩).lower ∧ (cell12769 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12769 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12769 ⟨18,by decide⟩).lower ∧ (cell12769 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12769 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12769 ⟨19,by decide⟩).lower ∧ (cell12769 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12769 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12769 ⟨20,by decide⟩).lower ∧ (cell12769 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12769 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12769 ⟨21,by decide⟩).lower ∧ (cell12769 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12769 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12769 ⟨22,by decide⟩).lower ∧ (cell12769 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12769 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12769 ⟨23,by decide⟩).lower ∧ (cell12769 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12769 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12769 ⟨24,by decide⟩).lower ∧ (cell12769 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12769 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12769 ⟨25,by decide⟩).lower ∧ (cell12769 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12769 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12769 ⟨26,by decide⟩).lower ∧ (cell12769 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12769 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12769 ⟨27,by decide⟩).lower ∧ (cell12769 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12769 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12769 ⟨28,by decide⟩).lower ∧ (cell12769 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12769 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12769 ⟨29,by decide⟩).lower ∧ (cell12769 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12769 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12769 ⟨30,by decide⟩).lower ∧ (cell12769 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12769 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12769 ⟨31,by decide⟩).lower ∧ (cell12769 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12769 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12769 ⟨32,by decide⟩).lower ∧ (cell12769 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12769 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12769 ⟨33,by decide⟩).lower ∧ (cell12769 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12769 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12769 ⟨34,by decide⟩).lower ∧ (cell12769 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12769 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12769 ⟨35,by decide⟩).lower ∧ (cell12769 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12769 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12769 ⟨36,by decide⟩).lower ∧ (cell12769 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12769 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12769 ⟨37,by decide⟩).lower ∧ (cell12769 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12769 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12769 ⟨38,by decide⟩).lower ∧ (cell12769 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12769 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12769 ⟨39,by decide⟩).lower ∧ (cell12769 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12769 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12769 ⟨40,by decide⟩).lower ∧ (cell12769 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12769 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12769 ⟨41,by decide⟩).lower ∧ (cell12769 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12769 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12769 ⟨42,by decide⟩).lower ∧ (cell12769 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12769 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12769 ⟨43,by decide⟩).lower ∧ (cell12769 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12769 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12769 ⟨44,by decide⟩).lower ∧ (cell12769 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12769 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12769 ⟨45,by decide⟩).lower ∧ (cell12769 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12769 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12769 ⟨46,by decide⟩).lower ∧ (cell12769 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12769 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12769 ⟨47,by decide⟩).lower ∧ (cell12769 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12769 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12769 ⟨48,by decide⟩).lower ∧ (cell12769 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12769 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12769 ⟨49,by decide⟩).lower ∧ (cell12769 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12769 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12769 ⟨50,by decide⟩).lower ∧ (cell12769 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12769 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12769 ⟨51,by decide⟩).lower ∧ (cell12769 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12769 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12769 ⟨52,by decide⟩).lower ∧ (cell12769 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12769 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12769 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12769 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12769,cell12769,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12769 i).lower ∧
    (cell12769 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12769 i).upper ≤ (0.532 : ℝ) ∧
    (cell12769 i).centre ≤ (0.1 : ℝ) ∧ (cell12769 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12769 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12769 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12769

/-! The local source numeric instances at 12769 have no network premises. -/
namespace BstLean.Part269.N12769
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12769)
open BstLean.Part268 (cell12769)

noncomputable def sourceNumerics12769 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12769 (cell12769 i)
      scalarRow12769.M scalarRow12769.H scalarRow12769.xi := by
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
    energy_allowance := scalarRow12769.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12769]
    centre_nonneg := (scalarRow12769.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12769])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12769
/-! Actual 12770 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12770 ≤ (1.035710078213 : ℝ) := by
  have hr : (113.004424692133 : ℝ) ≤ √(12770 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.004424692133 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12770 12770 (11 / 1000) ≤
    (0.008458845851 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12770) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.004424692133 : ℝ) ≤ √(12770 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12770)
  have hdiv : K / √(12770 : ℝ) ≤ K / 113.004424692133 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.004424692133 ≤ (0.008458845851 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12770.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12770 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12770 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12770 := gPlus_lower 12770
end BstLean.Part269.N12770

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12770
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035710078212 : ℝ) ≤ wn 12770 := by
  have hn : √(12770 : ℝ) ≤ 113.004424692134 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12770 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.004424692134 ≤ 2 / √(12770 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250476183 : ℝ) ≤ rhoBar 12770 BstLean.Part154.csC ∧
    rhoBar 12770 BstLean.Part154.csC ≤ 0.000250476571 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035710078212 : ℝ) / (1.295212 * 12770) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035710078213 : ℝ) / (1.29521 * 12770) := by gcongr
      _ ≤ (0.000250476571 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12770 BstLean.Part154.csC) ≤ 0.001001969023 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12770 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) ≤ 0.000191315645 ∧
    cc1 (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) ≤ 0.000121735425 ∧
    cc2 (rhoBar 12770 BstLean.Part154.csC) ≤ 0.000070668360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12770 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12770 BstLean.Part154.csC * nuR (rhoBar 12770 BstLean.Part154.csC)) ≤ 0.000500968827 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250476571 : ℝ) * 0.001001969023 := by gcongr
      _ ≤ (0.000500968827 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12770 BstLean.Part154.csC) * nuR (rhoBar 12770 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001969023 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12770 BstLean.Part154.csC) * rhoBar 12770 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250476571 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250476571 / 2 + 0.399 * 0.001001969023 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191315645 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500968827 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121735425 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250476571 / 1.414213562 := by gcongr
      _ ≤ (0.000070668360 : ℝ) := by norm_num

end BstLean.Part269.N12770

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12770
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) ≤ 1.58065E-7 := by
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12770 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12770 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191315645 : ℝ) ^ 2 + 0.000121735425 ^ 2 + 3 * 0.000070668360 ^ 2 +
        2 * 0.797885 * 0.000191315645 * 0.000121735425 + 2 * 0.000191315645 * 0.000070668360 +
        4 * 0.797885 * 0.000121735425 * 0.000070668360 := by gcongr
    _ ≤ (1.58065E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12770 BstLean.Part154.csC Θ ≤ 0.002614372538 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12770 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12770 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035710078213 * 1.58065E-7 / (0.000250476183 : ℝ) := by gcongr
    _ ≤ 0.002614372538 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12770 BstLean.Part154.csC Θ ≤ 0.002900512302 + 0.000660610567 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12770 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035710078213 : ℝ) * ((2 * Θ * 0.000250476571 +
        (6863 / 10000) * 0.000250476571 * 12770 * 0.001001969023) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002900512302 + 0.000660610567 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12770 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12770 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12770 0.011 Θ ∧ gammaRatio 12770 0.011 Θ ≤ 0.000086107368 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12770 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035710078213 : ℝ) * 0.525 / ((1 - 0.011) * 12770) := by gcongr
      _ ≤ (0.000086107368 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12770 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12770 0.011 Θ) :=
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
    badAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12770 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12770 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12770 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12770 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12770 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12770 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12770 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12770 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12770 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12770 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035710078213 : ℝ) * 12770 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003460673772 + 0.003274983105 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12770

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12770
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12770 BstLean.Part154.csC) (piBar (rhoBar 12770 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12770 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12770 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12770 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12770 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12770 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12770 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12770 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12770 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12770 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052338708507 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12770) ≤ 0.010568060360 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12770 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035710078213)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010568060360 + 2 * 0.737676 / 12770) := by gcongr
    _ ≤ (0.052338708507 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12770 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12770

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12770
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506716546 : ℝ) ≤ plow 12770 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12770) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686639903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372545583) : eMP 12770 0.011 xi bn ≤ 0.001181729653 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12770 : ℝ) * (1 - 0.011))) ≤ 0.000584311931 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372545583 / (12770 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584311931 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584311931 : ℝ) + 3.141593 * 0.052686639903 / (12770 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181729653 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686639903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372545583) : PiBarMP 12770 12 0.011 xi bn ≤ 0.160804000004 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12770 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037047882302 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.381181698716 : ℝ) ≤ √((12770 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.004424692133 : ℝ) ≤ √(12770 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12770) ≤ 0.123290820698 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037047882302 + 0.052686639903 * 1.772454 / (2 * (112.381181698716 : ℝ))) * (1 + 0.001181729653) +
        8 / (12770 * 113.004424692133) + 0.123290820698 := by gcongr
    _ ≤ (0.160804000004 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686639903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372545583) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281874413580) :
    parallelOracle 12770 0.011 xi bn cd ≤ 0.161789003417 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12770 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12770 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506716546 : ℝ) ≤ plow 12770 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.004424692133 : ℝ) ≤ √(12770 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281874413580 : ℝ) / (2 * 0.560506716546 * 113.004424692133)) * 0.160804000004 +
        0.281874413580 ^ 2 / (2 * 0.560506716546 * 113.004424692133) := by gcongr
    _ ≤ (0.161789003417 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686639903) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372545583)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281874413580) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12770 12770 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506716546 : ℝ) ≤ plow 12770 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.004424692133 : ℝ) ≤ √(12770 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12770 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12770 Θ 1.22 ≤ 0.011734943155 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.004424692133 := by gcongr <;> linarith
      _ ≤ (0.011734943155 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12770 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12770 12770 0.011 ≤ 0.008458845851 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12770 12770 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12770 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12770 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12770 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12770 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161789003417 + 0.011734943155 + (0.008458845851 : ℝ) *
        (1 + 2 * (0.281874413580 + 0.011734943155) / (0.560506716546 * 113.004424692133))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12770]

end BstLean.Part269.N12770

/-! The original eight local profiles supply actual 12770 moment certificates. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12770 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052686639903 ∧
    0 ≤ bN 12770 BstLean.Part154.csC (groupTheta g) ∧ bN 12770 BstLean.Part154.csC (groupTheta g) ≤ 0.001372545583 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12770 12770 0.011
      (momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12770 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12770 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12770 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229535705073 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12770 0.011
      (momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12770 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12770
/-! The actual computed-centre upper energy formula at 12770. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12770

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12770)
open BstLean.Part268 (cell12770)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085288709879
  | 2 => 0.086227814422
  | 3 => 0.087164536329
  | 4 => 0.088100172692
  | 5 => 0.089036296296
  | 6 => 0.089974797066
  | 7 => 0.090917927514
  | 8 => 0.091868352223
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12770 12770 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12770 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12770

/-! Actual upper energy certificates on all 43 source endpoints at 12770. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12770)
open BstLean.Part268 (cell12770)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12770 (gMinus 12770) (1 - (cell12770 i).lower) ≤ 1 ∧
    energyUpper 12770 (gMinus 12770) (BstLean.Part211.gPlus 12770)
      (finiteEnergy 12770 12770 0.011) (1 - (cell12770 i).lower) ≤
      (cell12770 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨10,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨11,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨12,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨13,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨14,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨15,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨16,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨17,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨18,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨19,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨20,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨21,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨22,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨23,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨24,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨25,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨26,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨27,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨28,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨29,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨30,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨31,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨32,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨33,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨34,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨35,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨36,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨37,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨38,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨39,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨40,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨41,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨42,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨43,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨44,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨45,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨46,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨47,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨48,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨49,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨50,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨51,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12770) (by norm_num)
        (q := 1 - (cell12770 ⟨52,by decide⟩).lower)
        (by norm_num [cell12770]) (by norm_num [cell12770])
      exact ⟨E.1,E.2.trans (by norm_num [cell12770])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12770

/-! Source-cell containment and simple scalar guards at 12770. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12770)
open BstLean.Part268 (cell12770)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12770 ⟨10,by decide⟩).lower ∧ (cell12770 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12770 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12770 ⟨11,by decide⟩).lower ∧ (cell12770 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12770 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12770 ⟨12,by decide⟩).lower ∧ (cell12770 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12770 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12770 ⟨13,by decide⟩).lower ∧ (cell12770 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12770 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12770 ⟨14,by decide⟩).lower ∧ (cell12770 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12770 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12770 ⟨15,by decide⟩).lower ∧ (cell12770 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12770 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12770 ⟨16,by decide⟩).lower ∧ (cell12770 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12770 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12770 ⟨17,by decide⟩).lower ∧ (cell12770 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12770 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12770 ⟨18,by decide⟩).lower ∧ (cell12770 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12770 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12770 ⟨19,by decide⟩).lower ∧ (cell12770 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12770 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12770 ⟨20,by decide⟩).lower ∧ (cell12770 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12770 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12770 ⟨21,by decide⟩).lower ∧ (cell12770 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12770 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12770 ⟨22,by decide⟩).lower ∧ (cell12770 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12770 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12770 ⟨23,by decide⟩).lower ∧ (cell12770 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12770 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12770 ⟨24,by decide⟩).lower ∧ (cell12770 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12770 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12770 ⟨25,by decide⟩).lower ∧ (cell12770 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12770 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12770 ⟨26,by decide⟩).lower ∧ (cell12770 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12770 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12770 ⟨27,by decide⟩).lower ∧ (cell12770 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12770 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12770 ⟨28,by decide⟩).lower ∧ (cell12770 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12770 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12770 ⟨29,by decide⟩).lower ∧ (cell12770 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12770 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12770 ⟨30,by decide⟩).lower ∧ (cell12770 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12770 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12770 ⟨31,by decide⟩).lower ∧ (cell12770 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12770 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12770 ⟨32,by decide⟩).lower ∧ (cell12770 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12770 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12770 ⟨33,by decide⟩).lower ∧ (cell12770 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12770 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12770 ⟨34,by decide⟩).lower ∧ (cell12770 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12770 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12770 ⟨35,by decide⟩).lower ∧ (cell12770 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12770 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12770 ⟨36,by decide⟩).lower ∧ (cell12770 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12770 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12770 ⟨37,by decide⟩).lower ∧ (cell12770 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12770 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12770 ⟨38,by decide⟩).lower ∧ (cell12770 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12770 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12770 ⟨39,by decide⟩).lower ∧ (cell12770 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12770 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12770 ⟨40,by decide⟩).lower ∧ (cell12770 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12770 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12770 ⟨41,by decide⟩).lower ∧ (cell12770 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12770 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12770 ⟨42,by decide⟩).lower ∧ (cell12770 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12770 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12770 ⟨43,by decide⟩).lower ∧ (cell12770 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12770 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12770 ⟨44,by decide⟩).lower ∧ (cell12770 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12770 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12770 ⟨45,by decide⟩).lower ∧ (cell12770 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12770 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12770 ⟨46,by decide⟩).lower ∧ (cell12770 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12770 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12770 ⟨47,by decide⟩).lower ∧ (cell12770 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12770 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12770 ⟨48,by decide⟩).lower ∧ (cell12770 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12770 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12770 ⟨49,by decide⟩).lower ∧ (cell12770 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12770 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12770 ⟨50,by decide⟩).lower ∧ (cell12770 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12770 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12770 ⟨51,by decide⟩).lower ∧ (cell12770 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12770 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12770 ⟨52,by decide⟩).lower ∧ (cell12770 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12770 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12770 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12770 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12770,cell12770,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12770 i).lower ∧
    (cell12770 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12770 i).upper ≤ (0.532 : ℝ) ∧
    (cell12770 i).centre ≤ (0.1 : ℝ) ∧ (cell12770 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12770 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12770 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12770

/-! The local source numeric instances at 12770 have no network premises. -/
namespace BstLean.Part269.N12770
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12770)
open BstLean.Part268 (cell12770)

noncomputable def sourceNumerics12770 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12770 (cell12770 i)
      scalarRow12770.M scalarRow12770.H scalarRow12770.xi := by
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
    energy_allowance := scalarRow12770.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12770]
    centre_nonneg := (scalarRow12770.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12770])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12770
/-! Actual 12771 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12771 ≤ (1.035708667829 : ℝ) := by
  have hr : (113.008849211024 : ℝ) ≤ √(12771 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.008849211024 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12771 12771 (11 / 1000) ≤
    (0.008458514668 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12771) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.008849211024 : ℝ) ≤ √(12771 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12771)
  have hdiv : K / √(12771 : ℝ) ≤ K / 113.008849211024 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.008849211024 ≤ (0.008458514668 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12771.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12771 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12771 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12771 := gPlus_lower 12771
end BstLean.Part269.N12771

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12771
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035708667828 : ℝ) ≤ wn 12771 := by
  have hn : √(12771 : ℝ) ≤ 113.008849211025 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12771 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.008849211025 ≤ 2 / √(12771 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250456229 : ℝ) ≤ rhoBar 12771 BstLean.Part154.csC ∧
    rhoBar 12771 BstLean.Part154.csC ≤ 0.000250456617 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035708667828 : ℝ) / (1.295212 * 12771) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035708667829 : ℝ) / (1.29521 * 12771) := by gcongr
      _ ≤ (0.000250456617 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12771 BstLean.Part154.csC) ≤ 0.001001889197 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12771 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) ≤ 0.000191300403 ∧
    cc1 (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) ≤ 0.000121725727 ∧
    cc2 (rhoBar 12771 BstLean.Part154.csC) ≤ 0.000070662730 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12771 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12771 BstLean.Part154.csC * nuR (rhoBar 12771 BstLean.Part154.csC)) ≤ 0.000500928917 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250456617 : ℝ) * 0.001001889197 := by gcongr
      _ ≤ (0.000500928917 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12771 BstLean.Part154.csC) * nuR (rhoBar 12771 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001889197 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12771 BstLean.Part154.csC) * rhoBar 12771 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250456617 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250456617 / 2 + 0.399 * 0.001001889197 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191300403 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500928917 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121725727 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250456617 / 1.414213562 := by gcongr
      _ ≤ (0.000070662730 : ℝ) := by norm_num

end BstLean.Part269.N12771

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12771
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) ≤ 1.58040E-7 := by
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12771 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12771 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191300403 : ℝ) ^ 2 + 0.000121725727 ^ 2 + 3 * 0.000070662730 ^ 2 +
        2 * 0.797885 * 0.000191300403 * 0.000121725727 + 2 * 0.000191300403 * 0.000070662730 +
        4 * 0.797885 * 0.000121725727 * 0.000070662730 := by gcongr
    _ ≤ (1.58040E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12771 BstLean.Part154.csC Θ ≤ 0.002614163737 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12771 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12771 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035708667829 * 1.58040E-7 / (0.000250456229 : ℝ) := by gcongr
    _ ≤ 0.002614163737 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12771 BstLean.Part154.csC Θ ≤ 0.002900273321 + 0.000660557041 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12771 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035708667829 : ℝ) * ((2 * Θ * 0.000250456617 +
        (6863 / 10000) * 0.000250456617 * 12771 * 0.001001889197) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002900273321 + 0.000660557041 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12771 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12771 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12771 0.011 Θ ∧ gammaRatio 12771 0.011 Θ ≤ 0.000086100508 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12771 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035708667829 : ℝ) * 0.525 / ((1 - 0.011) * 12771) := by gcongr
      _ ≤ (0.000086100508 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12771 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12771 0.011 Θ) :=
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
    badAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12771 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12771 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12771 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12771 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12771 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12771 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12771 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12771 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12771 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12771 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035708667829 : ℝ) * 12771 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003460434791 + 0.003274720778 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12771

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12771
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12771 BstLean.Part154.csC) (piBar (rhoBar 12771 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12771 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12771 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12771 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12771 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12771 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12771 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12771 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12771 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12771 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052336637187 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12771) ≤ 0.010567646600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12771 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035708667829)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010567646600 + 2 * 0.737676 / 12771) := by gcongr
    _ ≤ (0.052336637187 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12771 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12771

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12771
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506761271 : ℝ) ≤ plow 12771 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12771) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686263200)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372435962) : eMP 12771 0.011 xi bn ≤ 0.001181636113 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12771 : ℝ) * (1 - 0.011))) ≤ 0.000584265721 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372435962 / (12771 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584265721 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584265721 : ℝ) + 3.141593 * 0.052686263200 / (12771 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181636113 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686263200)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372435962) : PiBarMP 12771 12 0.011 xi bn ≤ 0.160797668283 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12771 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037046402822 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.385581815462 : ℝ) ≤ √((12771 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.008849211024 : ℝ) ≤ √(12771 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12771) ≤ 0.123285993620 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037046402822 + 0.052686263200 * 1.772454 / (2 * (112.385581815462 : ℝ))) * (1 + 0.001181636113) +
        8 / (12771 * 113.008849211024) + 0.123285993620 := by gcongr
    _ ≤ (0.160797668283 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686263200)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372435962) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281871521682) :
    parallelOracle 12771 0.011 xi bn cd ≤ 0.161782602425 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12771 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12771 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506761271 : ℝ) ≤ plow 12771 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.008849211024 : ℝ) ≤ √(12771 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281871521682 : ℝ) / (2 * 0.560506761271 * 113.008849211024)) * 0.160797668283 +
        0.281871521682 ^ 2 / (2 * 0.560506761271 * 113.008849211024) := by gcongr
    _ ≤ (0.161782602425 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052686263200) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372435962)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281871521682) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12771 12771 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506761271 : ℝ) ≤ plow 12771 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.008849211024 : ℝ) ≤ √(12771 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12771 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12771 Θ 1.22 ≤ 0.011734483709 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.008849211024 := by gcongr <;> linarith
      _ ≤ (0.011734483709 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12771 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12771 12771 0.011 ≤ 0.008458514668 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12771 12771 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12771 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12771 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12771 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12771 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161782602425 + 0.011734483709 + (0.008458514668 : ℝ) *
        (1 + 2 * (0.281871521682 + 0.011734483709) / (0.560506761271 * 113.008849211024))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12771]

end BstLean.Part269.N12771

/-! The original eight local profiles supply actual 12771 moment certificates. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12771 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052686263200 ∧
    0 ≤ bN 12771 BstLean.Part154.csC (groupTheta g) ∧ bN 12771 BstLean.Part154.csC (groupTheta g) ≤ 0.001372435962 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12771 12771 0.011
      (momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12771 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12771 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12771 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229534884495 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12771 0.011
      (momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12771 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12771
/-! The actual computed-centre upper energy formula at 12771. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12771

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12771)
open BstLean.Part268 (cell12771)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085285867354
  | 2 => 0.086224921316
  | 3 => 0.087161585532
  | 4 => 0.088097155434
  | 5 => 0.089033201857
  | 6 => 0.089971612442
  | 7 => 0.090914637041
  | 8 => 0.091864937165
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12771 12771 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12771 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12771

/-! Actual upper energy certificates on all 43 source endpoints at 12771. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12771)
open BstLean.Part268 (cell12771)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12771 (gMinus 12771) (1 - (cell12771 i).lower) ≤ 1 ∧
    energyUpper 12771 (gMinus 12771) (BstLean.Part211.gPlus 12771)
      (finiteEnergy 12771 12771 0.011) (1 - (cell12771 i).lower) ≤
      (cell12771 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨10,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨11,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨12,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨13,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨14,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨15,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨16,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨17,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨18,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨19,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨20,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨21,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨22,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨23,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨24,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨25,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨26,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨27,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨28,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨29,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨30,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨31,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨32,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨33,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨34,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨35,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨36,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨37,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨38,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨39,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨40,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨41,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨42,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨43,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨44,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨45,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨46,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨47,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨48,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨49,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨50,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨51,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12771) (by norm_num)
        (q := 1 - (cell12771 ⟨52,by decide⟩).lower)
        (by norm_num [cell12771]) (by norm_num [cell12771])
      exact ⟨E.1,E.2.trans (by norm_num [cell12771])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12771

/-! Source-cell containment and simple scalar guards at 12771. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12771)
open BstLean.Part268 (cell12771)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12771 ⟨10,by decide⟩).lower ∧ (cell12771 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12771 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12771 ⟨11,by decide⟩).lower ∧ (cell12771 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12771 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12771 ⟨12,by decide⟩).lower ∧ (cell12771 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12771 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12771 ⟨13,by decide⟩).lower ∧ (cell12771 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12771 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12771 ⟨14,by decide⟩).lower ∧ (cell12771 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12771 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12771 ⟨15,by decide⟩).lower ∧ (cell12771 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12771 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12771 ⟨16,by decide⟩).lower ∧ (cell12771 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12771 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12771 ⟨17,by decide⟩).lower ∧ (cell12771 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12771 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12771 ⟨18,by decide⟩).lower ∧ (cell12771 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12771 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12771 ⟨19,by decide⟩).lower ∧ (cell12771 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12771 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12771 ⟨20,by decide⟩).lower ∧ (cell12771 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12771 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12771 ⟨21,by decide⟩).lower ∧ (cell12771 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12771 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12771 ⟨22,by decide⟩).lower ∧ (cell12771 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12771 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12771 ⟨23,by decide⟩).lower ∧ (cell12771 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12771 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12771 ⟨24,by decide⟩).lower ∧ (cell12771 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12771 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12771 ⟨25,by decide⟩).lower ∧ (cell12771 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12771 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12771 ⟨26,by decide⟩).lower ∧ (cell12771 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12771 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12771 ⟨27,by decide⟩).lower ∧ (cell12771 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12771 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12771 ⟨28,by decide⟩).lower ∧ (cell12771 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12771 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12771 ⟨29,by decide⟩).lower ∧ (cell12771 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12771 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12771 ⟨30,by decide⟩).lower ∧ (cell12771 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12771 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12771 ⟨31,by decide⟩).lower ∧ (cell12771 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12771 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12771 ⟨32,by decide⟩).lower ∧ (cell12771 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12771 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12771 ⟨33,by decide⟩).lower ∧ (cell12771 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12771 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12771 ⟨34,by decide⟩).lower ∧ (cell12771 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12771 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12771 ⟨35,by decide⟩).lower ∧ (cell12771 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12771 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12771 ⟨36,by decide⟩).lower ∧ (cell12771 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12771 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12771 ⟨37,by decide⟩).lower ∧ (cell12771 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12771 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12771 ⟨38,by decide⟩).lower ∧ (cell12771 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12771 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12771 ⟨39,by decide⟩).lower ∧ (cell12771 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12771 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12771 ⟨40,by decide⟩).lower ∧ (cell12771 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12771 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12771 ⟨41,by decide⟩).lower ∧ (cell12771 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12771 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12771 ⟨42,by decide⟩).lower ∧ (cell12771 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12771 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12771 ⟨43,by decide⟩).lower ∧ (cell12771 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12771 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12771 ⟨44,by decide⟩).lower ∧ (cell12771 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12771 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12771 ⟨45,by decide⟩).lower ∧ (cell12771 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12771 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12771 ⟨46,by decide⟩).lower ∧ (cell12771 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12771 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12771 ⟨47,by decide⟩).lower ∧ (cell12771 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12771 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12771 ⟨48,by decide⟩).lower ∧ (cell12771 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12771 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12771 ⟨49,by decide⟩).lower ∧ (cell12771 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12771 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12771 ⟨50,by decide⟩).lower ∧ (cell12771 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12771 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12771 ⟨51,by decide⟩).lower ∧ (cell12771 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12771 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12771 ⟨52,by decide⟩).lower ∧ (cell12771 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12771 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12771 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12771 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12771,cell12771,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12771 i).lower ∧
    (cell12771 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12771 i).upper ≤ (0.532 : ℝ) ∧
    (cell12771 i).centre ≤ (0.1 : ℝ) ∧ (cell12771 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12771 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12771 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12771

/-! The local source numeric instances at 12771 have no network premises. -/
namespace BstLean.Part269.N12771
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12771)
open BstLean.Part268 (cell12771)

noncomputable def sourceNumerics12771 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12771 (cell12771 i)
      scalarRow12771.M scalarRow12771.H scalarRow12771.xi := by
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
    energy_allowance := scalarRow12771.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12771]
    centre_nonneg := (scalarRow12771.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12771])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12771
/-! Actual 12772 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12772 ≤ (1.035707257613 : ℝ) := by
  have hr : (113.013273556693 : ℝ) ≤ √(12772 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.013273556693 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12772 12772 (11 / 1000) ≤
    (0.008458183524 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12772) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.013273556693 : ℝ) ≤ √(12772 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12772)
  have hdiv : K / √(12772 : ℝ) ≤ K / 113.013273556693 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.013273556693 ≤ (0.008458183524 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12772.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12772 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12772 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12772 := gPlus_lower 12772
end BstLean.Part269.N12772

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12772
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035707257612 : ℝ) ≤ wn 12772 := by
  have hn : √(12772 : ℝ) ≤ 113.013273556694 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12772 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.013273556694 ≤ 2 / √(12772 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250436278 : ℝ) ≤ rhoBar 12772 BstLean.Part154.csC ∧
    rhoBar 12772 BstLean.Part154.csC ≤ 0.000250436666 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035707257612 : ℝ) / (1.295212 * 12772) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035707257613 : ℝ) / (1.29521 * 12772) := by gcongr
      _ ≤ (0.000250436666 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12772 BstLean.Part154.csC) ≤ 0.001001809383 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12772 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) ≤ 0.000191285164 ∧
    cc1 (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) ≤ 0.000121716030 ∧
    cc2 (rhoBar 12772 BstLean.Part154.csC) ≤ 0.000070657101 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12772 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12772 BstLean.Part154.csC * nuR (rhoBar 12772 BstLean.Part154.csC)) ≤ 0.000500889012 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250436666 : ℝ) * 0.001001809383 := by gcongr
      _ ≤ (0.000500889012 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12772 BstLean.Part154.csC) * nuR (rhoBar 12772 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001809383 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12772 BstLean.Part154.csC) * rhoBar 12772 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250436666 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250436666 / 2 + 0.399 * 0.001001809383 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191285164 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500889012 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121716030 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250436666 / 1.414213562 := by gcongr
      _ ≤ (0.000070657101 : ℝ) := by norm_num

end BstLean.Part269.N12772

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12772
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) ≤ 1.58015E-7 := by
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12772 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12772 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191285164 : ℝ) ^ 2 + 0.000121716030 ^ 2 + 3 * 0.000070657101 ^ 2 +
        2 * 0.797885 * 0.000191285164 * 0.000121716030 + 2 * 0.000191285164 * 0.000070657101 +
        4 * 0.797885 * 0.000121716030 * 0.000070657101 := by gcongr
    _ ≤ (1.58015E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12772 BstLean.Part154.csC Θ ≤ 0.002613954873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12772 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12772 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035707257613 * 1.58015E-7 / (0.000250436278 : ℝ) := by gcongr
    _ ≤ 0.002613954873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12772 BstLean.Part154.csC Θ ≤ 0.002900034376 + 0.000660503522 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12772 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035707257613 : ℝ) * ((2 * Θ * 0.000250436666 +
        (6863 / 10000) * 0.000250436666 * 12772 * 0.001001809383) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002900034376 + 0.000660503522 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12772 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12772 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12772 0.011 Θ ∧ gammaRatio 12772 0.011 Θ ≤ 0.000086093650 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12772 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035707257613 : ℝ) * 0.525 / ((1 - 0.011) * 12772) := by gcongr
      _ ≤ (0.000086093650 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12772 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12772 0.011 Θ) :=
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
    badAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12772 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12772 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12772 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12772 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12772 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12772 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12772 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12772 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12772 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12772 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035707257613 : ℝ) * 12772 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003460195846 + 0.003274458395 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12772

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12772
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12772 BstLean.Part154.csC) (piBar (rhoBar 12772 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12772 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12772 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12772 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12772 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12772 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12772 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12772 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12772 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12772 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052334566109 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12772) ≤ 0.010567232888 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12772 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035707257613)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010567232888 + 2 * 0.737676 / 12772) := by gcongr
    _ ≤ (0.052334566109 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12772 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12772

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12772
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506805989 : ℝ) ≤ plow 12772 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12772) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685886504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372326309) : eMP 12772 0.011 xi bn ≤ 0.001181542568 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12772 : ℝ) * (1 - 0.011))) ≤ 0.000584219508 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372326309 / (12772 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584219508 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584219508 : ℝ) + 3.141593 * 0.052685886504 / (12772 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181542568 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685886504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372326309) : PiBarMP 12772 12 0.011 xi bn ≤ 0.160791336638 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12772 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037044922851 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.389981759941 : ℝ) ≤ √((12772 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.013273556693 : ℝ) ≤ √(12772 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12772) ≤ 0.123281167108 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037044922851 + 0.052685886504 * 1.772454 / (2 * (112.389981759941 : ℝ))) * (1 + 0.001181542568) +
        8 / (12772 * 113.013273556693) + 0.123281167108 := by gcongr
    _ ≤ (0.160791336638 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685886504)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372326309) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281868630039) :
    parallelOracle 12772 0.011 xi bn cd ≤ 0.161776201518 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12772 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12772 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506805989 : ℝ) ≤ plow 12772 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.013273556693 : ℝ) ≤ √(12772 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281868630039 : ℝ) / (2 * 0.560506805989 * 113.013273556693)) * 0.160791336638 +
        0.281868630039 ^ 2 / (2 * 0.560506805989 * 113.013273556693) := by gcongr
    _ ≤ (0.161776201518 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685886504) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372326309)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281868630039) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12772 12772 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506805989 : ℝ) ≤ plow 12772 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.013273556693 : ℝ) ≤ √(12772 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12772 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12772 Θ 1.22 ≤ 0.011734024317 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.013273556693 := by gcongr <;> linarith
      _ ≤ (0.011734024317 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12772 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12772 12772 0.011 ≤ 0.008458183524 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12772 12772 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12772 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12772 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12772 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12772 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161776201518 + 0.011734024317 + (0.008458183524 : ℝ) *
        (1 + 2 * (0.281868630039 + 0.011734024317) / (0.560506805989 * 113.013273556693))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12772]

end BstLean.Part269.N12772

/-! The original eight local profiles supply actual 12772 moment certificates. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12772 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052685886504 ∧
    0 ≤ bN 12772 BstLean.Part154.csC (groupTheta g) ∧ bN 12772 BstLean.Part154.csC (groupTheta g) ≤ 0.001372326309 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12772 12772 0.011
      (momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12772 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12772 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12772 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229534063930 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12772 0.011
      (momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12772 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12772
/-! The actual computed-centre upper energy formula at 12772. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12772

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12772)
open BstLean.Part268 (cell12772)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085283025840
  | 2 => 0.086222029261
  | 3 => 0.087158635834
  | 4 => 0.088094139338
  | 5 => 0.089030108656
  | 6 => 0.089968429147
  | 7 => 0.090911348008
  | 8 => 0.091861523682
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12772 12772 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12772 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12772

/-! Actual upper energy certificates on all 43 source endpoints at 12772. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12772)
open BstLean.Part268 (cell12772)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12772 (gMinus 12772) (1 - (cell12772 i).lower) ≤ 1 ∧
    energyUpper 12772 (gMinus 12772) (BstLean.Part211.gPlus 12772)
      (finiteEnergy 12772 12772 0.011) (1 - (cell12772 i).lower) ≤
      (cell12772 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨10,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨11,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨12,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨13,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨14,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨15,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨16,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨17,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨18,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨19,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨20,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨21,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨22,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨23,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨24,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨25,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨26,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨27,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨28,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨29,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨30,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨31,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨32,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨33,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨34,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨35,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨36,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨37,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨38,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨39,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨40,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨41,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨42,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨43,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨44,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨45,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨46,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨47,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨48,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨49,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨50,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨51,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12772) (by norm_num)
        (q := 1 - (cell12772 ⟨52,by decide⟩).lower)
        (by norm_num [cell12772]) (by norm_num [cell12772])
      exact ⟨E.1,E.2.trans (by norm_num [cell12772])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12772

/-! Source-cell containment and simple scalar guards at 12772. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12772)
open BstLean.Part268 (cell12772)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12772 ⟨10,by decide⟩).lower ∧ (cell12772 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12772 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12772 ⟨11,by decide⟩).lower ∧ (cell12772 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12772 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12772 ⟨12,by decide⟩).lower ∧ (cell12772 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12772 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12772 ⟨13,by decide⟩).lower ∧ (cell12772 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12772 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12772 ⟨14,by decide⟩).lower ∧ (cell12772 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12772 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12772 ⟨15,by decide⟩).lower ∧ (cell12772 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12772 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12772 ⟨16,by decide⟩).lower ∧ (cell12772 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12772 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12772 ⟨17,by decide⟩).lower ∧ (cell12772 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12772 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12772 ⟨18,by decide⟩).lower ∧ (cell12772 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12772 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12772 ⟨19,by decide⟩).lower ∧ (cell12772 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12772 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12772 ⟨20,by decide⟩).lower ∧ (cell12772 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12772 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12772 ⟨21,by decide⟩).lower ∧ (cell12772 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12772 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12772 ⟨22,by decide⟩).lower ∧ (cell12772 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12772 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12772 ⟨23,by decide⟩).lower ∧ (cell12772 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12772 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12772 ⟨24,by decide⟩).lower ∧ (cell12772 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12772 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12772 ⟨25,by decide⟩).lower ∧ (cell12772 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12772 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12772 ⟨26,by decide⟩).lower ∧ (cell12772 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12772 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12772 ⟨27,by decide⟩).lower ∧ (cell12772 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12772 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12772 ⟨28,by decide⟩).lower ∧ (cell12772 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12772 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12772 ⟨29,by decide⟩).lower ∧ (cell12772 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12772 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12772 ⟨30,by decide⟩).lower ∧ (cell12772 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12772 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12772 ⟨31,by decide⟩).lower ∧ (cell12772 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12772 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12772 ⟨32,by decide⟩).lower ∧ (cell12772 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12772 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12772 ⟨33,by decide⟩).lower ∧ (cell12772 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12772 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12772 ⟨34,by decide⟩).lower ∧ (cell12772 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12772 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12772 ⟨35,by decide⟩).lower ∧ (cell12772 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12772 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12772 ⟨36,by decide⟩).lower ∧ (cell12772 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12772 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12772 ⟨37,by decide⟩).lower ∧ (cell12772 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12772 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12772 ⟨38,by decide⟩).lower ∧ (cell12772 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12772 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12772 ⟨39,by decide⟩).lower ∧ (cell12772 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12772 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12772 ⟨40,by decide⟩).lower ∧ (cell12772 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12772 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12772 ⟨41,by decide⟩).lower ∧ (cell12772 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12772 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12772 ⟨42,by decide⟩).lower ∧ (cell12772 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12772 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12772 ⟨43,by decide⟩).lower ∧ (cell12772 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12772 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12772 ⟨44,by decide⟩).lower ∧ (cell12772 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12772 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12772 ⟨45,by decide⟩).lower ∧ (cell12772 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12772 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12772 ⟨46,by decide⟩).lower ∧ (cell12772 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12772 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12772 ⟨47,by decide⟩).lower ∧ (cell12772 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12772 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12772 ⟨48,by decide⟩).lower ∧ (cell12772 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12772 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12772 ⟨49,by decide⟩).lower ∧ (cell12772 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12772 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12772 ⟨50,by decide⟩).lower ∧ (cell12772 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12772 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12772 ⟨51,by decide⟩).lower ∧ (cell12772 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12772 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12772 ⟨52,by decide⟩).lower ∧ (cell12772 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12772 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12772 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12772 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12772,cell12772,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12772 i).lower ∧
    (cell12772 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12772 i).upper ≤ (0.532 : ℝ) ∧
    (cell12772 i).centre ≤ (0.1 : ℝ) ∧ (cell12772 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12772 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12772 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12772

/-! The local source numeric instances at 12772 have no network premises. -/
namespace BstLean.Part269.N12772
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12772)
open BstLean.Part268 (cell12772)

noncomputable def sourceNumerics12772 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12772 (cell12772 i)
      scalarRow12772.M scalarRow12772.H scalarRow12772.xi := by
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
    energy_allowance := scalarRow12772.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12772]
    centre_nonneg := (scalarRow12772.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12772])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12772
/-! Actual 12773 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12773 ≤ (1.035705847563 : ℝ) := by
  have hr : (113.017697729160 : ℝ) ≤ √(12773 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.017697729160 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12773 12773 (11 / 1000) ≤
    (0.008457852419 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12773) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.017697729160 : ℝ) ≤ √(12773 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12773)
  have hdiv : K / √(12773 : ℝ) ≤ K / 113.017697729160 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.017697729160 ≤ (0.008457852419 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12773.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12773 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12773 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12773 := gPlus_lower 12773
end BstLean.Part269.N12773

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12773
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035705847562 : ℝ) ≤ wn 12773 := by
  have hn : √(12773 : ℝ) ≤ 113.017697729161 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12773 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.017697729161 ≤ 2 / √(12773 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250416330 : ℝ) ≤ rhoBar 12773 BstLean.Part154.csC ∧
    rhoBar 12773 BstLean.Part154.csC ≤ 0.000250416718 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035705847562 : ℝ) / (1.295212 * 12773) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035705847563 : ℝ) / (1.29521 * 12773) := by gcongr
      _ ≤ (0.000250416718 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12773 BstLean.Part154.csC) ≤ 0.001001729581 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12773 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) ≤ 0.000191269927 ∧
    cc1 (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) ≤ 0.000121706335 ∧
    cc2 (rhoBar 12773 BstLean.Part154.csC) ≤ 0.000070651473 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12773 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12773 BstLean.Part154.csC * nuR (rhoBar 12773 BstLean.Part154.csC)) ≤ 0.000500849114 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250416718 : ℝ) * 0.001001729581 := by gcongr
      _ ≤ (0.000500849114 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12773 BstLean.Part154.csC) * nuR (rhoBar 12773 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001729581 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12773 BstLean.Part154.csC) * rhoBar 12773 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250416718 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250416718 / 2 + 0.399 * 0.001001729581 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191269927 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500849114 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121706335 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250416718 / 1.414213562 := by gcongr
      _ ≤ (0.000070651473 : ℝ) := by norm_num

end BstLean.Part269.N12773

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12773
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) ≤ 1.57990E-7 := by
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12773 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12773 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191269927 : ℝ) ^ 2 + 0.000121706335 ^ 2 + 3 * 0.000070651473 ^ 2 +
        2 * 0.797885 * 0.000191269927 * 0.000121706335 + 2 * 0.000191269927 * 0.000070651473 +
        4 * 0.797885 * 0.000121706335 * 0.000070651473 := by gcongr
    _ ≤ (1.57990E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12773 BstLean.Part154.csC Θ ≤ 0.002613745947 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12773 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12773 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035705847563 * 1.57990E-7 / (0.000250416330 : ℝ) := by gcongr
    _ ≤ 0.002613745947 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12773 BstLean.Part154.csC Θ ≤ 0.002899795465 + 0.000660450012 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12773 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035705847563 : ℝ) * ((2 * Θ * 0.000250416718 +
        (6863 / 10000) * 0.000250416718 * 12773 * 0.001001729581) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002899795465 + 0.000660450012 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12773 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12773 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12773 0.011 Θ ∧ gammaRatio 12773 0.011 Θ ≤ 0.000086086792 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12773 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035705847563 : ℝ) * 0.525 / ((1 - 0.011) * 12773) := by gcongr
      _ ≤ (0.000086086792 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12773 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12773 0.011 Θ) :=
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
    badAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12773 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12773 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12773 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12773 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12773 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12773 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12773 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12773 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12773 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12773 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035705847563 : ℝ) * 12773 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003459956935 + 0.003274195959 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12773

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12773
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12773 BstLean.Part154.csC) (piBar (rhoBar 12773 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12773 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12773 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12773 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12773 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12773 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12773 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12773 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12773 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12773 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052332495277 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12773) ≤ 0.010566819225 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12773 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035705847563)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010566819225 + 2 * 0.737676 / 12773) := by gcongr
    _ ≤ (0.052332495277 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12773 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12773

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12773
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506850700 : ℝ) ≤ plow 12773 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12773) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685509814)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372216623) : eMP 12773 0.011 xi bn ≤ 0.001181449014 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12773 : ℝ) * (1 - 0.011))) ≤ 0.000584173291 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372216623 / (12773 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584173291 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584173291 : ℝ) + 3.141593 * 0.052685509814 / (12773 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181449014 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685509814)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372216623) : PiBarMP 12773 12 0.011 xi bn ≤ 0.160785005058 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12773 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037043442376 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.394381532174 : ℝ) ≤ √((12773 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.017697729160 : ℝ) ≤ √(12773 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12773) ≤ 0.123276341164 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037043442376 + 0.052685509814 * 1.772454 / (2 * (112.394381532174 : ℝ))) * (1 + 0.001181449014) +
        8 / (12773 * 113.017697729160) + 0.123276341164 := by gcongr
    _ ≤ (0.160785005058 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685509814)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372216623) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281865738652) :
    parallelOracle 12773 0.011 xi bn cd ≤ 0.161769800685 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12773 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12773 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506850700 : ℝ) ≤ plow 12773 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.017697729160 : ℝ) ≤ √(12773 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281865738652 : ℝ) / (2 * 0.560506850700 * 113.017697729160)) * 0.160785005058 +
        0.281865738652 ^ 2 / (2 * 0.560506850700 * 113.017697729160) := by gcongr
    _ ≤ (0.161769800685 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685509814) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372216623)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281865738652) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12773 12773 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506850700 : ℝ) ≤ plow 12773 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.017697729160 : ℝ) ≤ √(12773 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12773 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12773 Θ 1.22 ≤ 0.011733564979 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.017697729160 := by gcongr <;> linarith
      _ ≤ (0.011733564979 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12773 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12773 12773 0.011 ≤ 0.008457852419 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12773 12773 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12773 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12773 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12773 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12773 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161769800685 + 0.011733564979 + (0.008457852419 : ℝ) *
        (1 + 2 * (0.281865738652 + 0.011733564979) / (0.560506850700 * 113.017697729160))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12773]

end BstLean.Part269.N12773

/-! The original eight local profiles supply actual 12773 moment certificates. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12773 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052685509814 ∧
    0 ≤ bN 12773 BstLean.Part154.csC (groupTheta g) ∧ bN 12773 BstLean.Part154.csC (groupTheta g) ≤ 0.001372216623 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12773 12773 0.011
      (momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12773 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12773 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12773 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229533243375 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12773 0.011
      (momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12773 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12773
/-! The actual computed-centre upper energy formula at 12773. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12773

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12773)
open BstLean.Part268 (cell12773)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085280185333
  | 2 => 0.086219138255
  | 3 => 0.087155687236
  | 4 => 0.088091124403
  | 5 => 0.089027016690
  | 6 => 0.089965247179
  | 7 => 0.090908060413
  | 8 => 0.091858111770
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12773 12773 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12773 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12773

/-! Actual upper energy certificates on all 43 source endpoints at 12773. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12773)
open BstLean.Part268 (cell12773)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12773 (gMinus 12773) (1 - (cell12773 i).lower) ≤ 1 ∧
    energyUpper 12773 (gMinus 12773) (BstLean.Part211.gPlus 12773)
      (finiteEnergy 12773 12773 0.011) (1 - (cell12773 i).lower) ≤
      (cell12773 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨10,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨11,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨12,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨13,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨14,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨15,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨16,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨17,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨18,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨19,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨20,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨21,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨22,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨23,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨24,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨25,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨26,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨27,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨28,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨29,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨30,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨31,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨32,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨33,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨34,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨35,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨36,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨37,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨38,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨39,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨40,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨41,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨42,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨43,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨44,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨45,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨46,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨47,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨48,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨49,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨50,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨51,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12773) (by norm_num)
        (q := 1 - (cell12773 ⟨52,by decide⟩).lower)
        (by norm_num [cell12773]) (by norm_num [cell12773])
      exact ⟨E.1,E.2.trans (by norm_num [cell12773])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12773

/-! Source-cell containment and simple scalar guards at 12773. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12773)
open BstLean.Part268 (cell12773)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12773 ⟨10,by decide⟩).lower ∧ (cell12773 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12773 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12773 ⟨11,by decide⟩).lower ∧ (cell12773 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12773 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12773 ⟨12,by decide⟩).lower ∧ (cell12773 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12773 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12773 ⟨13,by decide⟩).lower ∧ (cell12773 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12773 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12773 ⟨14,by decide⟩).lower ∧ (cell12773 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12773 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12773 ⟨15,by decide⟩).lower ∧ (cell12773 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12773 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12773 ⟨16,by decide⟩).lower ∧ (cell12773 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12773 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12773 ⟨17,by decide⟩).lower ∧ (cell12773 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12773 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12773 ⟨18,by decide⟩).lower ∧ (cell12773 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12773 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12773 ⟨19,by decide⟩).lower ∧ (cell12773 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12773 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12773 ⟨20,by decide⟩).lower ∧ (cell12773 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12773 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12773 ⟨21,by decide⟩).lower ∧ (cell12773 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12773 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12773 ⟨22,by decide⟩).lower ∧ (cell12773 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12773 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12773 ⟨23,by decide⟩).lower ∧ (cell12773 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12773 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12773 ⟨24,by decide⟩).lower ∧ (cell12773 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12773 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12773 ⟨25,by decide⟩).lower ∧ (cell12773 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12773 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12773 ⟨26,by decide⟩).lower ∧ (cell12773 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12773 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12773 ⟨27,by decide⟩).lower ∧ (cell12773 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12773 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12773 ⟨28,by decide⟩).lower ∧ (cell12773 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12773 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12773 ⟨29,by decide⟩).lower ∧ (cell12773 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12773 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12773 ⟨30,by decide⟩).lower ∧ (cell12773 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12773 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12773 ⟨31,by decide⟩).lower ∧ (cell12773 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12773 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12773 ⟨32,by decide⟩).lower ∧ (cell12773 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12773 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12773 ⟨33,by decide⟩).lower ∧ (cell12773 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12773 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12773 ⟨34,by decide⟩).lower ∧ (cell12773 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12773 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12773 ⟨35,by decide⟩).lower ∧ (cell12773 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12773 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12773 ⟨36,by decide⟩).lower ∧ (cell12773 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12773 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12773 ⟨37,by decide⟩).lower ∧ (cell12773 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12773 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12773 ⟨38,by decide⟩).lower ∧ (cell12773 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12773 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12773 ⟨39,by decide⟩).lower ∧ (cell12773 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12773 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12773 ⟨40,by decide⟩).lower ∧ (cell12773 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12773 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12773 ⟨41,by decide⟩).lower ∧ (cell12773 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12773 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12773 ⟨42,by decide⟩).lower ∧ (cell12773 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12773 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12773 ⟨43,by decide⟩).lower ∧ (cell12773 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12773 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12773 ⟨44,by decide⟩).lower ∧ (cell12773 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12773 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12773 ⟨45,by decide⟩).lower ∧ (cell12773 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12773 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12773 ⟨46,by decide⟩).lower ∧ (cell12773 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12773 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12773 ⟨47,by decide⟩).lower ∧ (cell12773 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12773 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12773 ⟨48,by decide⟩).lower ∧ (cell12773 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12773 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12773 ⟨49,by decide⟩).lower ∧ (cell12773 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12773 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12773 ⟨50,by decide⟩).lower ∧ (cell12773 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12773 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12773 ⟨51,by decide⟩).lower ∧ (cell12773 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12773 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12773 ⟨52,by decide⟩).lower ∧ (cell12773 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12773 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12773 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12773 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12773,cell12773,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12773 i).lower ∧
    (cell12773 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12773 i).upper ≤ (0.532 : ℝ) ∧
    (cell12773 i).centre ≤ (0.1 : ℝ) ∧ (cell12773 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12773 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12773 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12773

/-! The local source numeric instances at 12773 have no network premises. -/
namespace BstLean.Part269.N12773
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12773)
open BstLean.Part268 (cell12773)

noncomputable def sourceNumerics12773 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12773 (cell12773 i)
      scalarRow12773.M scalarRow12773.H scalarRow12773.xi := by
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
    energy_allowance := scalarRow12773.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12773]
    centre_nonneg := (scalarRow12773.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12773])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12773
/-! Actual 12774 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12774 ≤ (1.035704437680 : ℝ) := by
  have hr : (113.022121728447 : ℝ) ≤ √(12774 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.022121728447 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12774 12774 (11 / 1000) ≤
    (0.008457521353 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12774) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.022121728447 : ℝ) ≤ √(12774 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12774)
  have hdiv : K / √(12774 : ℝ) ≤ K / 113.022121728447 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.022121728447 ≤ (0.008457521353 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12774.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12774 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12774 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12774 := gPlus_lower 12774
end BstLean.Part269.N12774

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12774
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035704437679 : ℝ) ≤ wn 12774 := by
  have hn : √(12774 : ℝ) ≤ 113.022121728448 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12774 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.022121728448 ≤ 2 / √(12774 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250396386 : ℝ) ≤ rhoBar 12774 BstLean.Part154.csC ∧
    rhoBar 12774 BstLean.Part154.csC ≤ 0.000250396774 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035704437679 : ℝ) / (1.295212 * 12774) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035704437680 : ℝ) / (1.29521 * 12774) := by gcongr
      _ ≤ (0.000250396774 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12774 BstLean.Part154.csC) ≤ 0.001001649795 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12774 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) ≤ 0.000191254693 ∧
    cc1 (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) ≤ 0.000121696642 ∧
    cc2 (rhoBar 12774 BstLean.Part154.csC) ≤ 0.000070645846 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12774 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12774 BstLean.Part154.csC * nuR (rhoBar 12774 BstLean.Part154.csC)) ≤ 0.000500809223 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250396774 : ℝ) * 0.001001649795 := by gcongr
      _ ≤ (0.000500809223 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12774 BstLean.Part154.csC) * nuR (rhoBar 12774 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001001649795 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12774 BstLean.Part154.csC) * rhoBar 12774 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250396774 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250396774 / 2 + 0.399 * 0.001001649795 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191254693 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000500809223 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121696642 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250396774 / 1.414213562 := by gcongr
      _ ≤ (0.000070645846 : ℝ) := by norm_num

end BstLean.Part269.N12774

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12774
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) ≤ 1.57965E-7 := by
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12774 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12774 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191254693 : ℝ) ^ 2 + 0.000121696642 ^ 2 + 3 * 0.000070645846 ^ 2 +
        2 * 0.797885 * 0.000191254693 * 0.000121696642 + 2 * 0.000191254693 * 0.000070645846 +
        4 * 0.797885 * 0.000121696642 * 0.000070645846 := by gcongr
    _ ≤ (1.57965E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12774 BstLean.Part154.csC Θ ≤ 0.002613536947 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12774 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12774 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035704437680 * 1.57965E-7 / (0.000250396386 : ℝ) := by gcongr
    _ ≤ 0.002613536947 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12774 BstLean.Part154.csC Θ ≤ 0.002899556613 + 0.000660396513 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12774 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035704437680 : ℝ) * ((2 * Θ * 0.000250396774 +
        (6863 / 10000) * 0.000250396774 * 12774 * 0.001001649795) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002899556613 + 0.000660396513 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12774 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12774 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12774 0.011 Θ ∧ gammaRatio 12774 0.011 Θ ≤ 0.000086079936 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12774 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035704437680 : ℝ) * 0.525 / ((1 - 0.011) * 12774) := by gcongr
      _ ≤ (0.000086079936 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12774 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12774 0.011 Θ) :=
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
    badAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12774 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12774 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12774 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12774 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12774 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12774 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12774 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12774 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12774 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12774 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035704437680 : ℝ) * 12774 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003459718083 + 0.003273933460 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12774

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12774
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12774 BstLean.Part154.csC) (piBar (rhoBar 12774 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12774 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12774 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12774 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12774 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12774 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12774 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12774 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12774 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12774 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052330424688 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12774) ≤ 0.010566405610 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12774 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035704437680)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010566405610 + 2 * 0.737676 / 12774) := by gcongr
    _ ≤ (0.052330424688 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12774 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12774

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12774
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506895404 : ℝ) ≤ plow 12774 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12774) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685133150)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372106898) : eMP 12774 0.011 xi bn ≤ 0.001181355453 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12774 : ℝ) * (1 - 0.011))) ≤ 0.000584127070 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001372106898 / (12774 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584127070 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584127070 : ℝ) + 3.141593 * 0.052685133150 / (12774 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001181355453 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685133150)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372106898) : PiBarMP 12774 12 0.011 xi bn ≤ 0.160778673461 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12774 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037041961315 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.398781132181 : ℝ) ≤ √((12774 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.022121728447 : ℝ) ≤ √(12774 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12774) ≤ 0.123271515786 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037041961315 + 0.052685133150 * 1.772454 / (2 * (112.398781132181 : ℝ))) * (1 + 0.001181355453) +
        8 / (12774 * 113.022121728447) + 0.123271515786 := by gcongr
    _ ≤ (0.160778673461 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685133150)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372106898) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281862847562) :
    parallelOracle 12774 0.011 xi bn cd ≤ 0.161763399844 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12774 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12774 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506895404 : ℝ) ≤ plow 12774 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.022121728447 : ℝ) ≤ √(12774 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281862847562 : ℝ) / (2 * 0.560506895404 * 113.022121728447)) * 0.160778673461 +
        0.281862847562 ^ 2 / (2 * 0.560506895404 * 113.022121728447) := by gcongr
    _ ≤ (0.161763399844 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052685133150) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001372106898)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281862847562) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12774 12774 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506895404 : ℝ) ≤ plow 12774 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.022121728447 : ℝ) ≤ √(12774 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12774 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12774 Θ 1.22 ≤ 0.011733105694 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.022121728447 := by gcongr <;> linarith
      _ ≤ (0.011733105694 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12774 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12774 12774 0.011 ≤ 0.008457521353 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12774 12774 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12774 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12774 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12774 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12774 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161763399844 + 0.011733105694 + (0.008457521353 : ℝ) *
        (1 + 2 * (0.281862847562 + 0.011733105694) / (0.560506895404 * 113.022121728447))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12774]

end BstLean.Part269.N12774

/-! The original eight local profiles supply actual 12774 moment certificates. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12774 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052685133150 ∧
    0 ≤ bN 12774 BstLean.Part154.csC (groupTheta g) ∧ bN 12774 BstLean.Part154.csC (groupTheta g) ≤ 0.001372106898 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12774 12774 0.011
      (momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12774 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12774 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12774 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229532422874 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12774 0.011
      (momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12774 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12774
/-! The actual computed-centre upper energy formula at 12774. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12774

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12774)
open BstLean.Part268 (cell12774)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085277345834
  | 2 => 0.086216248297
  | 3 => 0.087152739735
  | 4 => 0.088088110626
  | 5 => 0.089023925960
  | 6 => 0.089962066537
  | 7 => 0.090904774255
  | 8 => 0.091854701430
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12774 12774 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12774 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003465461536 + 0.003280300441 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S16.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S16.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12774

/-! Actual upper energy certificates on all 43 source endpoints at 12774. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12774)
open BstLean.Part268 (cell12774)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12774 (gMinus 12774) (1 - (cell12774 i).lower) ≤ 1 ∧
    energyUpper 12774 (gMinus 12774) (BstLean.Part211.gPlus 12774)
      (finiteEnergy 12774 12774 0.011) (1 - (cell12774 i).lower) ≤
      (cell12774 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨10,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨11,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨12,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨13,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨14,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨15,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨16,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨17,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨18,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨19,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨20,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨21,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨22,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨23,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨24,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨25,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨26,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨27,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨28,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨29,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨30,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨31,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨32,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨33,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨34,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨35,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨36,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨37,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨38,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨39,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨40,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨41,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨42,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨43,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨44,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨45,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨46,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨47,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨48,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨49,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨50,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨51,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12774) (by norm_num)
        (q := 1 - (cell12774 ⟨52,by decide⟩).lower)
        (by norm_num [cell12774]) (by norm_num [cell12774])
      exact ⟨E.1,E.2.trans (by norm_num [cell12774])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12774

/-! Source-cell containment and simple scalar guards at 12774. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12774)
open BstLean.Part268 (cell12774)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12774 ⟨10,by decide⟩).lower ∧ (cell12774 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12774 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12774 ⟨11,by decide⟩).lower ∧ (cell12774 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12774 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12774 ⟨12,by decide⟩).lower ∧ (cell12774 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12774 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12774 ⟨13,by decide⟩).lower ∧ (cell12774 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12774 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12774 ⟨14,by decide⟩).lower ∧ (cell12774 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12774 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12774 ⟨15,by decide⟩).lower ∧ (cell12774 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12774 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12774 ⟨16,by decide⟩).lower ∧ (cell12774 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12774 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12774 ⟨17,by decide⟩).lower ∧ (cell12774 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12774 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12774 ⟨18,by decide⟩).lower ∧ (cell12774 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12774 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12774 ⟨19,by decide⟩).lower ∧ (cell12774 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12774 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12774 ⟨20,by decide⟩).lower ∧ (cell12774 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12774 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12774 ⟨21,by decide⟩).lower ∧ (cell12774 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12774 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12774 ⟨22,by decide⟩).lower ∧ (cell12774 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12774 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12774 ⟨23,by decide⟩).lower ∧ (cell12774 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12774 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12774 ⟨24,by decide⟩).lower ∧ (cell12774 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12774 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12774 ⟨25,by decide⟩).lower ∧ (cell12774 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12774 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12774 ⟨26,by decide⟩).lower ∧ (cell12774 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12774 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12774 ⟨27,by decide⟩).lower ∧ (cell12774 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12774 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12774 ⟨28,by decide⟩).lower ∧ (cell12774 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12774 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12774 ⟨29,by decide⟩).lower ∧ (cell12774 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12774 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12774 ⟨30,by decide⟩).lower ∧ (cell12774 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12774 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12774 ⟨31,by decide⟩).lower ∧ (cell12774 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12774 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12774 ⟨32,by decide⟩).lower ∧ (cell12774 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12774 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12774 ⟨33,by decide⟩).lower ∧ (cell12774 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12774 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12774 ⟨34,by decide⟩).lower ∧ (cell12774 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12774 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12774 ⟨35,by decide⟩).lower ∧ (cell12774 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12774 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12774 ⟨36,by decide⟩).lower ∧ (cell12774 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12774 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12774 ⟨37,by decide⟩).lower ∧ (cell12774 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12774 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12774 ⟨38,by decide⟩).lower ∧ (cell12774 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12774 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12774 ⟨39,by decide⟩).lower ∧ (cell12774 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12774 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12774 ⟨40,by decide⟩).lower ∧ (cell12774 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12774 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12774 ⟨41,by decide⟩).lower ∧ (cell12774 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12774 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12774 ⟨42,by decide⟩).lower ∧ (cell12774 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12774 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12774 ⟨43,by decide⟩).lower ∧ (cell12774 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12774 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12774 ⟨44,by decide⟩).lower ∧ (cell12774 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12774 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12774 ⟨45,by decide⟩).lower ∧ (cell12774 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12774 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12774 ⟨46,by decide⟩).lower ∧ (cell12774 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12774 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12774 ⟨47,by decide⟩).lower ∧ (cell12774 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12774 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12774 ⟨48,by decide⟩).lower ∧ (cell12774 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12774 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12774 ⟨49,by decide⟩).lower ∧ (cell12774 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12774 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12774 ⟨50,by decide⟩).lower ∧ (cell12774 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12774 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12774 ⟨51,by decide⟩).lower ∧ (cell12774 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12774 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12774 ⟨52,by decide⟩).lower ∧ (cell12774 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12774 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12774 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12774 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12774,cell12774,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12774 i).lower ∧
    (cell12774 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12774 i).upper ≤ (0.532 : ℝ) ∧
    (cell12774 i).centre ≤ (0.1 : ℝ) ∧ (cell12774 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12774 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12774 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12774

/-! The local source numeric instances at 12774 have no network premises. -/
namespace BstLean.Part269.N12774
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12774)
open BstLean.Part268 (cell12774)

noncomputable def sourceNumerics12774 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12774 (cell12774 i)
      scalarRow12774.M scalarRow12774.H scalarRow12774.xi := by
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
    energy_allowance := scalarRow12774.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12774]
    centre_nonneg := (scalarRow12774.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12774])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12774