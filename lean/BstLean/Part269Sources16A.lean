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
/-! Actual 12750 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12750 ≤ (1.035738320912 : ℝ) := by
  have hr : (112.915897906362 : ℝ) ≤ √(12750 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.915897906362 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12750 12750 (11 / 1000) ≤
    (0.008465477691 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12750) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.915897906362 : ℝ) ≤ √(12750 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12750)
  have hdiv : K / √(12750 : ℝ) ≤ K / 112.915897906362 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.915897906362 ≤ (0.008465477691 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12750.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12750 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12750 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12750 := gPlus_lower 12750
end BstLean.Part269.N12750

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12750
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035738320911 : ℝ) ≤ wn 12750 := by
  have hn : √(12750 : ℝ) ≤ 112.915897906363 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12750 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.915897906363 ≤ 2 / √(12750 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250875927 : ℝ) ≤ rhoBar 12750 BstLean.Part154.csC ∧
    rhoBar 12750 BstLean.Part154.csC ≤ 0.000250876316 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035738320911 : ℝ) / (1.295212 * 12750) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035738320912 : ℝ) / (1.29521 * 12750) := by gcongr
      _ ≤ (0.000250876316 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12750 BstLean.Part154.csC) ≤ 0.001003568203 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12750 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) ≤ 0.000191620987 ∧
    cc1 (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) ≤ 0.000121929714 ∧
    cc2 (rhoBar 12750 BstLean.Part154.csC) ≤ 0.000070781142 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12750 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12750 BstLean.Part154.csC * nuR (rhoBar 12750 BstLean.Part154.csC)) ≤ 0.000501768367 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250876316 : ℝ) * 0.001003568203 := by gcongr
      _ ≤ (0.000501768367 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12750 BstLean.Part154.csC) * nuR (rhoBar 12750 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003568203 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12750 BstLean.Part154.csC) * rhoBar 12750 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250876316 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250876316 / 2 + 0.399 * 0.001003568203 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191620987 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501768367 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121929714 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250876316 / 1.414213562 := by gcongr
      _ ≤ (0.000070781142 : ℝ) := by norm_num

end BstLean.Part269.N12750

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12750
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) ≤ 1.58570E-7 := by
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12750 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12750 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191620987 : ℝ) ^ 2 + 0.000121929714 ^ 2 + 3 * 0.000070781142 ^ 2 +
        2 * 0.797885 * 0.000191620987 * 0.000121929714 + 2 * 0.000191620987 * 0.000070781142 +
        4 * 0.797885 * 0.000121929714 * 0.000070781142 := by gcongr
    _ ≤ (1.58570E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12750 BstLean.Part154.csC Θ ≤ 0.002618617538 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12750 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12750 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035738320912 * 1.58570E-7 / (0.000250875927 : ℝ) := by gcongr
    _ ≤ 0.002618617538 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12750 BstLean.Part154.csC Θ ≤ 0.002905300066 + 0.000661682903 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12750 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035738320912 : ℝ) * ((2 * Θ * 0.000250876316 +
        (6863 / 10000) * 0.000250876316 * 12750 * 0.001003568203) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002905300066 + 0.000661682903 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12750 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12750 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12750 0.011 Θ ∧ gammaRatio 12750 0.011 Θ ≤ 0.000086244790 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12750 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035738320912 : ℝ) * 0.525 / ((1 - 0.011) * 12750) := by gcongr
      _ ≤ (0.000086244790 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12750 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12750 0.011 Θ) :=
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
    badAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12750 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12750 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12750 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12750 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12750 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12750 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12750 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12750 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12750 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12750 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035738320912 : ℝ) * 12750 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465461536 + 0.003280300441 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12750

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12750
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12750 BstLean.Part154.csC) (piBar (rhoBar 12750 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12750 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12750 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12750 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12750 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12750 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12750 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12750 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12750 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12750 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052380186479 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12750) ≤ 0.010576345787 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12750 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035738320912)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010576345787 + 2 * 0.737676 / 12750) := by gcongr
    _ ≤ (0.052380186479 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12750 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12750

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12750
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505820572 : ℝ) ≤ plow 12750 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12750) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694219268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374774208) : eMP 12750 0.011 xi bn ≤ 0.001183617426 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12750 : ℝ) * (1 - 0.011))) ≤ 0.000585244594 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374774208 / (12750 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585244594 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585244594 : ℝ) + 3.141593 * 0.052694219268 / (12750 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183617426 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694219268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374774208) : PiBarMP 12750 12 0.011 xi bn ≤ 0.160931231598 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12750 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037077947732 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.293143156650 : ℝ) ≤ √((12750 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.915897906362 : ℝ) ≤ √(12750 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12750) ≤ 0.123387481490 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037077947732 + 0.052694219268 * 1.772454 / (2 * (112.293143156650 : ℝ))) * (1 + 0.001183617426) +
        8 / (12750 * 112.915897906362) + 0.123387481490 := by gcongr
    _ ≤ (0.160931231598 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694219268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374774208) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281932401167) :
    parallelOracle 12750 0.011 xi bn cd ≤ 0.161917624171 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12750 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12750 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505820572 : ℝ) ≤ plow 12750 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.915897906362 : ℝ) ≤ √(12750 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281932401167 : ℝ) / (2 * 0.560505820572 * 112.915897906362)) * 0.160931231598 +
        0.281932401167 ^ 2 / (2 * 0.560505820572 * 112.915897906362) := by gcongr
    _ ≤ (0.161917624171 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052694219268) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374774208)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281932401167) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12750 12750 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505820572 : ℝ) ≤ plow 12750 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.915897906362 : ℝ) ≤ √(12750 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12750 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12750 Θ 1.22 ≤ 0.011744143426 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.915897906362 := by gcongr <;> linarith
      _ ≤ (0.011744143426 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12750 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12750 12750 0.011 ≤ 0.008465477691 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12750 12750 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12750 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12750 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12750 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12750 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161917624171 + 0.011744143426 + (0.008465477691 : ℝ) *
        (1 + 2 * (0.281932401167 + 0.011744143426) / (0.560505820572 * 112.915897906362))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12750]

end BstLean.Part269.N12750

/-! The original eight local profiles supply actual 12750 moment certificates. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12750 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052694219268 ∧
    0 ≤ bN 12750 BstLean.Part154.csC (groupTheta g) ∧ bN 12750 BstLean.Part154.csC (groupTheta g) ≤ 0.001374774208 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12750 12750 0.011
      (momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12750 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12750 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12750 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229552214688 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12750 0.011
      (momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12750 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12750
/-! The actual computed-centre upper energy formula at 12750. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12750

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12750)
open BstLean.Part268 (cell12750)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085345773902
  | 2 => 0.086285898669
  | 3 => 0.087223785051
  | 4 => 0.088160763687
  | 5 => 0.089098446885
  | 6 => 0.090038770826
  | 7 => 0.090984041802
  | 8 => 0.091936986549
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12750 12750 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12750 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12750

/-! Actual upper energy certificates on all 43 source endpoints at 12750. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12750)
open BstLean.Part268 (cell12750)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12750 (gMinus 12750) (1 - (cell12750 i).lower) ≤ 1 ∧
    energyUpper 12750 (gMinus 12750) (BstLean.Part211.gPlus 12750)
      (finiteEnergy 12750 12750 0.011) (1 - (cell12750 i).lower) ≤
      (cell12750 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨10,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨11,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨12,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨13,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨14,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨15,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨16,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨17,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨18,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨19,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨20,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨21,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨22,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨23,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨24,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨25,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨26,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨27,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨28,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨29,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨30,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨31,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨32,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨33,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨34,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨35,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨36,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨37,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨38,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨39,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨40,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨41,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨42,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨43,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨44,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨45,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨46,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨47,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨48,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨49,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨50,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨51,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12750) (by norm_num)
        (q := 1 - (cell12750 ⟨52,by decide⟩).lower)
        (by norm_num [cell12750]) (by norm_num [cell12750])
      exact ⟨E.1,E.2.trans (by norm_num [cell12750])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12750

/-! Source-cell containment and simple scalar guards at 12750. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12750)
open BstLean.Part268 (cell12750)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12750 ⟨10,by decide⟩).lower ∧ (cell12750 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12750 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12750 ⟨11,by decide⟩).lower ∧ (cell12750 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12750 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12750 ⟨12,by decide⟩).lower ∧ (cell12750 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12750 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12750 ⟨13,by decide⟩).lower ∧ (cell12750 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12750 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12750 ⟨14,by decide⟩).lower ∧ (cell12750 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12750 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12750 ⟨15,by decide⟩).lower ∧ (cell12750 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12750 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12750 ⟨16,by decide⟩).lower ∧ (cell12750 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12750 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12750 ⟨17,by decide⟩).lower ∧ (cell12750 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12750 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12750 ⟨18,by decide⟩).lower ∧ (cell12750 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12750 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12750 ⟨19,by decide⟩).lower ∧ (cell12750 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12750 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12750 ⟨20,by decide⟩).lower ∧ (cell12750 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12750 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12750 ⟨21,by decide⟩).lower ∧ (cell12750 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12750 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12750 ⟨22,by decide⟩).lower ∧ (cell12750 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12750 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12750 ⟨23,by decide⟩).lower ∧ (cell12750 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12750 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12750 ⟨24,by decide⟩).lower ∧ (cell12750 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12750 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12750 ⟨25,by decide⟩).lower ∧ (cell12750 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12750 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12750 ⟨26,by decide⟩).lower ∧ (cell12750 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12750 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12750 ⟨27,by decide⟩).lower ∧ (cell12750 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12750 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12750 ⟨28,by decide⟩).lower ∧ (cell12750 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12750 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12750 ⟨29,by decide⟩).lower ∧ (cell12750 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12750 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12750 ⟨30,by decide⟩).lower ∧ (cell12750 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12750 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12750 ⟨31,by decide⟩).lower ∧ (cell12750 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12750 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12750 ⟨32,by decide⟩).lower ∧ (cell12750 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12750 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12750 ⟨33,by decide⟩).lower ∧ (cell12750 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12750 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12750 ⟨34,by decide⟩).lower ∧ (cell12750 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12750 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12750 ⟨35,by decide⟩).lower ∧ (cell12750 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12750 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12750 ⟨36,by decide⟩).lower ∧ (cell12750 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12750 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12750 ⟨37,by decide⟩).lower ∧ (cell12750 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12750 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12750 ⟨38,by decide⟩).lower ∧ (cell12750 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12750 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12750 ⟨39,by decide⟩).lower ∧ (cell12750 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12750 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12750 ⟨40,by decide⟩).lower ∧ (cell12750 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12750 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12750 ⟨41,by decide⟩).lower ∧ (cell12750 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12750 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12750 ⟨42,by decide⟩).lower ∧ (cell12750 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12750 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12750 ⟨43,by decide⟩).lower ∧ (cell12750 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12750 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12750 ⟨44,by decide⟩).lower ∧ (cell12750 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12750 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12750 ⟨45,by decide⟩).lower ∧ (cell12750 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12750 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12750 ⟨46,by decide⟩).lower ∧ (cell12750 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12750 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12750 ⟨47,by decide⟩).lower ∧ (cell12750 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12750 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12750 ⟨48,by decide⟩).lower ∧ (cell12750 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12750 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12750 ⟨49,by decide⟩).lower ∧ (cell12750 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12750 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12750 ⟨50,by decide⟩).lower ∧ (cell12750 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12750 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12750 ⟨51,by decide⟩).lower ∧ (cell12750 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12750 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12750 ⟨52,by decide⟩).lower ∧ (cell12750 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12750 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12750 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12750 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12750,cell12750,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12750 i).lower ∧
    (cell12750 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12750 i).upper ≤ (0.532 : ℝ) ∧
    (cell12750 i).centre ≤ (0.1 : ℝ) ∧ (cell12750 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12750 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12750 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12750

/-! The local source numeric instances at 12750 have no network premises. -/
namespace BstLean.Part269.N12750
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12750)
open BstLean.Part268 (cell12750)

noncomputable def sourceNumerics12750 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12750 (cell12750 i)
      scalarRow12750.M scalarRow12750.H scalarRow12750.xi := by
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
    energy_allowance := scalarRow12750.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12750]
    centre_nonneg := (scalarRow12750.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12750])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12750
/-! Actual 12751 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12751 ≤ (1.035736907190 : ℝ) := by
  have hr : (112.920325893968 : ℝ) ≤ √(12751 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.920325893968 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12751 12751 (11 / 1000) ≤
    (0.008465145729 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12751) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.920325893968 : ℝ) ≤ √(12751 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12751)
  have hdiv : K / √(12751 : ℝ) ≤ K / 112.920325893968 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.920325893968 ≤ (0.008465145729 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12751.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12751 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12751 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12751 := gPlus_lower 12751
end BstLean.Part269.N12751

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12751
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035736907189 : ℝ) ≤ wn 12751 := by
  have hn : √(12751 : ℝ) ≤ 112.920325893969 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12751 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.920325893969 ≤ 2 / √(12751 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250855910 : ℝ) ≤ rhoBar 12751 BstLean.Part154.csC ∧
    rhoBar 12751 BstLean.Part154.csC ≤ 0.000250856298 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035736907189 : ℝ) / (1.295212 * 12751) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035736907190 : ℝ) / (1.29521 * 12751) := by gcongr
      _ ≤ (0.000250856298 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12751 BstLean.Part154.csC) ≤ 0.001003488121 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12751 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) ≤ 0.000191605696 ∧
    cc1 (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) ≤ 0.000121919984 ∧
    cc2 (rhoBar 12751 BstLean.Part154.csC) ≤ 0.000070775494 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12751 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12751 BstLean.Part154.csC * nuR (rhoBar 12751 BstLean.Part154.csC)) ≤ 0.000501728329 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250856298 : ℝ) * 0.001003488121 := by gcongr
      _ ≤ (0.000501728329 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12751 BstLean.Part154.csC) * nuR (rhoBar 12751 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003488121 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12751 BstLean.Part154.csC) * rhoBar 12751 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250856298 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250856298 / 2 + 0.399 * 0.001003488121 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191605696 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501728329 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121919984 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250856298 / 1.414213562 := by gcongr
      _ ≤ (0.000070775494 : ℝ) := by norm_num

end BstLean.Part269.N12751

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12751
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) ≤ 1.58545E-7 := by
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12751 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12751 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191605696 : ℝ) ^ 2 + 0.000121919984 ^ 2 + 3 * 0.000070775494 ^ 2 +
        2 * 0.797885 * 0.000191605696 * 0.000121919984 + 2 * 0.000191605696 * 0.000070775494 +
        4 * 0.797885 * 0.000121919984 * 0.000070775494 := by gcongr
    _ ≤ (1.58545E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12751 BstLean.Part154.csC Θ ≤ 0.002618410034 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12751 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12751 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035736907190 * 1.58545E-7 / (0.000250855910 : ℝ) := by gcongr
    _ ≤ 0.002618410034 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12751 BstLean.Part154.csC Θ ≤ 0.002905060294 + 0.000661629203 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12751 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035736907190 : ℝ) * ((2 * Θ * 0.000250856298 +
        (6863 / 10000) * 0.000250856298 * 12751 * 0.001003488121) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002905060294 + 0.000661629203 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12751 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12751 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12751 0.011 Θ ∧ gammaRatio 12751 0.011 Θ ≤ 0.000086237909 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12751 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035736907190 : ℝ) * 0.525 / ((1 - 0.011) * 12751) := by gcongr
      _ ≤ (0.000086237909 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12751 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12751 0.011 Θ) :=
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
    badAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12751 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12751 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12751 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12751 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12751 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12751 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12751 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12751 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12751 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12751 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035736907190 : ℝ) * 12751 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003465221764 + 0.003280039237 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12751

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12751
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12751 BstLean.Part154.csC) (piBar (rhoBar 12751 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12751 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12751 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12751 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12751 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12751 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12751 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12751 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12751 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12751 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052378110248 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12751) ≤ 0.010575931053 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12751 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035736907190)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010575931053 + 2 * 0.737676 / 12751) := by gcongr
    _ ≤ (0.052378110248 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12751 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12751

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12751
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505865438 : ℝ) ≤ plow 12751 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12751) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693842364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374665268) : eMP 12751 0.011 xi bn ≤ 0.001183524028 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12751 : ℝ) * (1 - 0.011))) ≤ 0.000585198457 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374665268 / (12751 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585198457 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585198457 : ℝ) + 3.141593 * 0.052693842364 / (12751 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183524028 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693842364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374665268) : PiBarMP 12751 12 0.011 xi bn ≤ 0.160924898862 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12751 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037076478636 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.297546722980 : ℝ) ≤ √((12751 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.920325893968 : ℝ) ≤ √(12751 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12751) ≤ 0.123382643049 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037076478636 + 0.052693842364 * 1.772454 / (2 * (112.297546722980 : ℝ))) * (1 + 0.001183524028) +
        8 / (12751 * 112.920325893968) + 0.123382643049 := by gcongr
    _ ≤ (0.160924898862 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693842364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374665268) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281929503980) :
    parallelOracle 12751 0.011 xi bn cd ≤ 0.161911221984 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12751 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12751 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505865438 : ℝ) ≤ plow 12751 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.920325893968 : ℝ) ≤ √(12751 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281929503980 : ℝ) / (2 * 0.560505865438 * 112.920325893968)) * 0.160924898862 +
        0.281929503980 ^ 2 / (2 * 0.560505865438 * 112.920325893968) := by gcongr
    _ ≤ (0.161911221984 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693842364) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374665268)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281929503980) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12751 12751 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505865438 : ℝ) ≤ plow 12751 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.920325893968 : ℝ) ≤ √(12751 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12751 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12751 Θ 1.22 ≤ 0.011743682898 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.920325893968 := by gcongr <;> linarith
      _ ≤ (0.011743682898 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12751 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12751 12751 0.011 ≤ 0.008465145729 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12751 12751 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12751 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12751 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12751 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12751 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161911221984 + 0.011743682898 + (0.008465145729 : ℝ) *
        (1 + 2 * (0.281929503980 + 0.011743682898) / (0.560505865438 * 112.920325893968))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12751]

end BstLean.Part269.N12751

/-! The original eight local profiles supply actual 12751 moment certificates. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12751 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052693842364 ∧
    0 ≤ bN 12751 BstLean.Part154.csC (groupTheta g) ∧ bN 12751 BstLean.Part154.csC (groupTheta g) ≤ 0.001374665268 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12751 12751 0.011
      (momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12751 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12751 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12751 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229551393732 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12751 0.011
      (momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12751 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12751
/-! The actual computed-centre upper energy formula at 12751. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12751

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12751)
open BstLean.Part268 (cell12751)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085342910977
  | 2 => 0.086282984340
  | 3 => 0.087220812013
  | 4 => 0.088157722939
  | 5 => 0.089095327428
  | 6 => 0.090035559323
  | 7 => 0.090980722199
  | 8 => 0.091933539650
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12751 12751 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12751 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12751

/-! Actual upper energy certificates on all 43 source endpoints at 12751. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12751)
open BstLean.Part268 (cell12751)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12751 (gMinus 12751) (1 - (cell12751 i).lower) ≤ 1 ∧
    energyUpper 12751 (gMinus 12751) (BstLean.Part211.gPlus 12751)
      (finiteEnergy 12751 12751 0.011) (1 - (cell12751 i).lower) ≤
      (cell12751 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨10,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨11,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨12,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨13,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨14,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨15,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨16,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨17,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨18,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨19,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨20,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨21,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨22,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨23,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨24,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨25,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨26,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨27,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨28,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨29,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨30,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨31,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨32,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨33,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨34,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨35,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨36,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨37,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨38,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨39,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨40,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨41,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨42,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨43,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨44,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨45,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨46,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨47,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨48,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨49,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨50,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨51,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12751) (by norm_num)
        (q := 1 - (cell12751 ⟨52,by decide⟩).lower)
        (by norm_num [cell12751]) (by norm_num [cell12751])
      exact ⟨E.1,E.2.trans (by norm_num [cell12751])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12751

/-! Source-cell containment and simple scalar guards at 12751. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12751)
open BstLean.Part268 (cell12751)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12751 ⟨10,by decide⟩).lower ∧ (cell12751 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12751 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12751 ⟨11,by decide⟩).lower ∧ (cell12751 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12751 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12751 ⟨12,by decide⟩).lower ∧ (cell12751 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12751 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12751 ⟨13,by decide⟩).lower ∧ (cell12751 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12751 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12751 ⟨14,by decide⟩).lower ∧ (cell12751 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12751 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12751 ⟨15,by decide⟩).lower ∧ (cell12751 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12751 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12751 ⟨16,by decide⟩).lower ∧ (cell12751 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12751 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12751 ⟨17,by decide⟩).lower ∧ (cell12751 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12751 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12751 ⟨18,by decide⟩).lower ∧ (cell12751 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12751 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12751 ⟨19,by decide⟩).lower ∧ (cell12751 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12751 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12751 ⟨20,by decide⟩).lower ∧ (cell12751 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12751 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12751 ⟨21,by decide⟩).lower ∧ (cell12751 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12751 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12751 ⟨22,by decide⟩).lower ∧ (cell12751 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12751 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12751 ⟨23,by decide⟩).lower ∧ (cell12751 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12751 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12751 ⟨24,by decide⟩).lower ∧ (cell12751 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12751 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12751 ⟨25,by decide⟩).lower ∧ (cell12751 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12751 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12751 ⟨26,by decide⟩).lower ∧ (cell12751 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12751 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12751 ⟨27,by decide⟩).lower ∧ (cell12751 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12751 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12751 ⟨28,by decide⟩).lower ∧ (cell12751 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12751 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12751 ⟨29,by decide⟩).lower ∧ (cell12751 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12751 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12751 ⟨30,by decide⟩).lower ∧ (cell12751 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12751 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12751 ⟨31,by decide⟩).lower ∧ (cell12751 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12751 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12751 ⟨32,by decide⟩).lower ∧ (cell12751 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12751 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12751 ⟨33,by decide⟩).lower ∧ (cell12751 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12751 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12751 ⟨34,by decide⟩).lower ∧ (cell12751 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12751 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12751 ⟨35,by decide⟩).lower ∧ (cell12751 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12751 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12751 ⟨36,by decide⟩).lower ∧ (cell12751 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12751 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12751 ⟨37,by decide⟩).lower ∧ (cell12751 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12751 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12751 ⟨38,by decide⟩).lower ∧ (cell12751 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12751 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12751 ⟨39,by decide⟩).lower ∧ (cell12751 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12751 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12751 ⟨40,by decide⟩).lower ∧ (cell12751 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12751 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12751 ⟨41,by decide⟩).lower ∧ (cell12751 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12751 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12751 ⟨42,by decide⟩).lower ∧ (cell12751 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12751 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12751 ⟨43,by decide⟩).lower ∧ (cell12751 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12751 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12751 ⟨44,by decide⟩).lower ∧ (cell12751 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12751 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12751 ⟨45,by decide⟩).lower ∧ (cell12751 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12751 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12751 ⟨46,by decide⟩).lower ∧ (cell12751 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12751 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12751 ⟨47,by decide⟩).lower ∧ (cell12751 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12751 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12751 ⟨48,by decide⟩).lower ∧ (cell12751 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12751 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12751 ⟨49,by decide⟩).lower ∧ (cell12751 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12751 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12751 ⟨50,by decide⟩).lower ∧ (cell12751 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12751 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12751 ⟨51,by decide⟩).lower ∧ (cell12751 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12751 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12751 ⟨52,by decide⟩).lower ∧ (cell12751 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12751 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12751 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12751 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12751,cell12751,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12751 i).lower ∧
    (cell12751 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12751 i).upper ≤ (0.532 : ℝ) ∧
    (cell12751 i).centre ≤ (0.1 : ℝ) ∧ (cell12751 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12751 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12751 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12751

/-! The local source numeric instances at 12751 have no network premises. -/
namespace BstLean.Part269.N12751
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12751)
open BstLean.Part268 (cell12751)

noncomputable def sourceNumerics12751 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12751 (cell12751 i)
      scalarRow12751.M scalarRow12751.H scalarRow12751.xi := by
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
    energy_allowance := scalarRow12751.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12751]
    centre_nonneg := (scalarRow12751.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12751])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12751
/-! Actual 12752 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12752 ≤ (1.035735493635 : ℝ) := by
  have hr : (112.924753707944 : ℝ) ≤ √(12752 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.924753707944 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12752 12752 (11 / 1000) ≤
    (0.008464813805 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12752) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.924753707944 : ℝ) ≤ √(12752 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12752)
  have hdiv : K / √(12752 : ℝ) ≤ K / 112.924753707944 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.924753707944 ≤ (0.008464813805 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12752.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12752 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12752 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12752 := gPlus_lower 12752
end BstLean.Part269.N12752

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12752
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035735493634 : ℝ) ≤ wn 12752 := by
  have hn : √(12752 : ℝ) ≤ 112.924753707945 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12752 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.924753707945 ≤ 2 / √(12752 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250835896 : ℝ) ≤ rhoBar 12752 BstLean.Part154.csC ∧
    rhoBar 12752 BstLean.Part154.csC ≤ 0.000250836284 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035735493634 : ℝ) / (1.295212 * 12752) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035735493635 : ℝ) / (1.29521 * 12752) := by gcongr
      _ ≤ (0.000250836284 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12752 BstLean.Part154.csC) ≤ 0.001003408055 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12752 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) ≤ 0.000191590409 ∧
    cc1 (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) ≤ 0.000121910257 ∧
    cc2 (rhoBar 12752 BstLean.Part154.csC) ≤ 0.000070769847 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12752 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12752 BstLean.Part154.csC * nuR (rhoBar 12752 BstLean.Part154.csC)) ≤ 0.000501688298 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250836284 : ℝ) * 0.001003408055 := by gcongr
      _ ≤ (0.000501688298 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12752 BstLean.Part154.csC) * nuR (rhoBar 12752 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003408055 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12752 BstLean.Part154.csC) * rhoBar 12752 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250836284 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250836284 / 2 + 0.399 * 0.001003408055 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191590409 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501688298 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121910257 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250836284 / 1.414213562 := by gcongr
      _ ≤ (0.000070769847 : ℝ) := by norm_num

end BstLean.Part269.N12752

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12752
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) ≤ 1.58520E-7 := by
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12752 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12752 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191590409 : ℝ) ^ 2 + 0.000121910257 ^ 2 + 3 * 0.000070769847 ^ 2 +
        2 * 0.797885 * 0.000191590409 * 0.000121910257 + 2 * 0.000191590409 * 0.000070769847 +
        4 * 0.797885 * 0.000121910257 * 0.000070769847 := by gcongr
    _ ≤ (1.58520E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12752 BstLean.Part154.csC Θ ≤ 0.002618202468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12752 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12752 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035735493635 * 1.58520E-7 / (0.000250835896 : ℝ) := by gcongr
    _ ≤ 0.002618202468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12752 BstLean.Part154.csC Θ ≤ 0.002904820580 + 0.000661575514 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12752 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035735493635 : ℝ) * ((2 * Θ * 0.000250836284 +
        (6863 / 10000) * 0.000250836284 * 12752 * 0.001003408055) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002904820580 + 0.000661575514 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12752 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12752 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12752 0.011 Θ ∧ gammaRatio 12752 0.011 Θ ≤ 0.000086231028 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12752 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035735493635 : ℝ) * 0.525 / ((1 - 0.011) * 12752) := by gcongr
      _ ≤ (0.000086231028 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12752 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12752 0.011 Θ) :=
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
    badAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12752 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12752 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12752 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12752 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12752 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12752 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12752 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12752 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12752 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12752 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035735493635 : ℝ) * 12752 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464982050 + 0.003279777982 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12752

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12752
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12752 BstLean.Part154.csC) (piBar (rhoBar 12752 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12752 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12752 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12752 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12752 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12752 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12752 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12752 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12752 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12752 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052376034259 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12752) ≤ 0.010575516367 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12752 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035735493635)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010575516367 + 2 * 0.737676 / 12752) := by gcongr
    _ ≤ (0.052376034259 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12752 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12752

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12752
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505910296 : ℝ) ≤ plow 12752 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12752) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693465491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374556296) : eMP 12752 0.011 xi bn ≤ 0.001183430623 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12752 : ℝ) * (1 - 0.011))) ≤ 0.000585152316 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374556296 / (12752 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585152316 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585152316 : ℝ) + 3.141593 * 0.052693465491 / (12752 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183430623 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693465491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374556296) : PiBarMP 12752 12 0.011 xi bn ≤ 0.160918566207 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12752 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037075009050 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.301950116638 : ℝ) ≤ √((12752 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.924753707944 : ℝ) ≤ √(12752 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12752) ≤ 0.123377805178 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037075009050 + 0.052693465491 * 1.772454 / (2 * (112.301950116638 : ℝ))) * (1 + 0.001183430623) +
        8 / (12752 * 112.924753707944) + 0.123377805178 := by gcongr
    _ ≤ (0.160918566207 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693465491)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374556296) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281926607099) :
    parallelOracle 12752 0.011 xi bn cd ≤ 0.161904819886 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12752 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12752 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505910296 : ℝ) ≤ plow 12752 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.924753707944 : ℝ) ≤ √(12752 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281926607099 : ℝ) / (2 * 0.560505910296 * 112.924753707944)) * 0.160918566207 +
        0.281926607099 ^ 2 / (2 * 0.560505910296 * 112.924753707944) := by gcongr
    _ ≤ (0.161904819886 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693465491) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374556296)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281926607099) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12752 12752 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505910296 : ℝ) ≤ plow 12752 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.924753707944 : ℝ) ≤ √(12752 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12752 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12752 Θ 1.22 ≤ 0.011743222425 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.924753707944 := by gcongr <;> linarith
      _ ≤ (0.011743222425 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12752 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12752 12752 0.011 ≤ 0.008464813805 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12752 12752 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12752 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12752 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12752 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12752 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161904819886 + 0.011743222425 + (0.008464813805 : ℝ) *
        (1 + 2 * (0.281926607099 + 0.011743222425) / (0.560505910296 * 112.924753707944))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12752]

end BstLean.Part269.N12752

/-! The original eight local profiles supply actual 12752 moment certificates. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12752 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052693465491 ∧
    0 ≤ bN 12752 BstLean.Part154.csC (groupTheta g) ∧ bN 12752 BstLean.Part154.csC (groupTheta g) ≤ 0.001374556296 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12752 12752 0.011
      (momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12752 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12752 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12752 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229550572840 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12752 0.011
      (momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12752 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12752
/-! The actual computed-centre upper energy formula at 12752. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12752

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12752)
open BstLean.Part268 (cell12752)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085340049081
  | 2 => 0.086280071082
  | 3 => 0.087217840098
  | 4 => 0.088154683377
  | 5 => 0.089092209235
  | 6 => 0.090032349178
  | 7 => 0.090977404067
  | 8 => 0.091930094360
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12752 12752 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12752 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12752

/-! Actual upper energy certificates on all 43 source endpoints at 12752. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12752)
open BstLean.Part268 (cell12752)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12752 (gMinus 12752) (1 - (cell12752 i).lower) ≤ 1 ∧
    energyUpper 12752 (gMinus 12752) (BstLean.Part211.gPlus 12752)
      (finiteEnergy 12752 12752 0.011) (1 - (cell12752 i).lower) ≤
      (cell12752 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨10,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨11,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨12,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨13,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨14,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨15,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨16,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨17,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨18,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨19,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨20,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨21,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨22,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨23,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨24,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨25,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨26,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨27,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨28,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨29,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨30,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨31,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨32,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨33,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨34,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨35,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨36,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨37,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨38,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨39,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨40,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨41,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨42,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨43,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨44,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨45,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨46,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨47,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨48,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨49,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨50,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨51,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12752) (by norm_num)
        (q := 1 - (cell12752 ⟨52,by decide⟩).lower)
        (by norm_num [cell12752]) (by norm_num [cell12752])
      exact ⟨E.1,E.2.trans (by norm_num [cell12752])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12752

/-! Source-cell containment and simple scalar guards at 12752. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12752)
open BstLean.Part268 (cell12752)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12752 ⟨10,by decide⟩).lower ∧ (cell12752 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12752 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12752 ⟨11,by decide⟩).lower ∧ (cell12752 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12752 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12752 ⟨12,by decide⟩).lower ∧ (cell12752 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12752 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12752 ⟨13,by decide⟩).lower ∧ (cell12752 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12752 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12752 ⟨14,by decide⟩).lower ∧ (cell12752 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12752 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12752 ⟨15,by decide⟩).lower ∧ (cell12752 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12752 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12752 ⟨16,by decide⟩).lower ∧ (cell12752 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12752 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12752 ⟨17,by decide⟩).lower ∧ (cell12752 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12752 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12752 ⟨18,by decide⟩).lower ∧ (cell12752 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12752 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12752 ⟨19,by decide⟩).lower ∧ (cell12752 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12752 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12752 ⟨20,by decide⟩).lower ∧ (cell12752 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12752 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12752 ⟨21,by decide⟩).lower ∧ (cell12752 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12752 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12752 ⟨22,by decide⟩).lower ∧ (cell12752 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12752 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12752 ⟨23,by decide⟩).lower ∧ (cell12752 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12752 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12752 ⟨24,by decide⟩).lower ∧ (cell12752 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12752 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12752 ⟨25,by decide⟩).lower ∧ (cell12752 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12752 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12752 ⟨26,by decide⟩).lower ∧ (cell12752 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12752 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12752 ⟨27,by decide⟩).lower ∧ (cell12752 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12752 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12752 ⟨28,by decide⟩).lower ∧ (cell12752 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12752 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12752 ⟨29,by decide⟩).lower ∧ (cell12752 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12752 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12752 ⟨30,by decide⟩).lower ∧ (cell12752 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12752 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12752 ⟨31,by decide⟩).lower ∧ (cell12752 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12752 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12752 ⟨32,by decide⟩).lower ∧ (cell12752 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12752 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12752 ⟨33,by decide⟩).lower ∧ (cell12752 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12752 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12752 ⟨34,by decide⟩).lower ∧ (cell12752 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12752 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12752 ⟨35,by decide⟩).lower ∧ (cell12752 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12752 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12752 ⟨36,by decide⟩).lower ∧ (cell12752 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12752 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12752 ⟨37,by decide⟩).lower ∧ (cell12752 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12752 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12752 ⟨38,by decide⟩).lower ∧ (cell12752 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12752 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12752 ⟨39,by decide⟩).lower ∧ (cell12752 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12752 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12752 ⟨40,by decide⟩).lower ∧ (cell12752 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12752 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12752 ⟨41,by decide⟩).lower ∧ (cell12752 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12752 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12752 ⟨42,by decide⟩).lower ∧ (cell12752 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12752 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12752 ⟨43,by decide⟩).lower ∧ (cell12752 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12752 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12752 ⟨44,by decide⟩).lower ∧ (cell12752 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12752 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12752 ⟨45,by decide⟩).lower ∧ (cell12752 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12752 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12752 ⟨46,by decide⟩).lower ∧ (cell12752 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12752 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12752 ⟨47,by decide⟩).lower ∧ (cell12752 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12752 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12752 ⟨48,by decide⟩).lower ∧ (cell12752 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12752 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12752 ⟨49,by decide⟩).lower ∧ (cell12752 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12752 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12752 ⟨50,by decide⟩).lower ∧ (cell12752 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12752 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12752 ⟨51,by decide⟩).lower ∧ (cell12752 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12752 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12752 ⟨52,by decide⟩).lower ∧ (cell12752 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12752 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12752 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12752 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12752,cell12752,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12752 i).lower ∧
    (cell12752 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12752 i).upper ≤ (0.532 : ℝ) ∧
    (cell12752 i).centre ≤ (0.1 : ℝ) ∧ (cell12752 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12752 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12752 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12752

/-! The local source numeric instances at 12752 have no network premises. -/
namespace BstLean.Part269.N12752
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12752)
open BstLean.Part268 (cell12752)

noncomputable def sourceNumerics12752 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12752 (cell12752 i)
      scalarRow12752.M scalarRow12752.H scalarRow12752.xi := by
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
    energy_allowance := scalarRow12752.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12752]
    centre_nonneg := (scalarRow12752.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12752])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12752
/-! Actual 12753 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12753 ≤ (1.035734080248 : ℝ) := by
  have hr : (112.929181348312 : ℝ) ≤ √(12753 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.929181348312 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12753 12753 (11 / 1000) ≤
    (0.008464481921 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12753) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.929181348312 : ℝ) ≤ √(12753 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12753)
  have hdiv : K / √(12753 : ℝ) ≤ K / 112.929181348312 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.929181348312 ≤ (0.008464481921 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12753.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12753 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12753 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12753 := gPlus_lower 12753
end BstLean.Part269.N12753

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12753
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035734080247 : ℝ) ≤ wn 12753 := by
  have hn : √(12753 : ℝ) ≤ 112.929181348313 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12753 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.929181348313 ≤ 2 / √(12753 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250815885 : ℝ) ≤ rhoBar 12753 BstLean.Part154.csC ∧
    rhoBar 12753 BstLean.Part154.csC ≤ 0.000250816273 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035734080247 : ℝ) / (1.295212 * 12753) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035734080248 : ℝ) / (1.29521 * 12753) := by gcongr
      _ ≤ (0.000250816273 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12753 BstLean.Part154.csC) ≤ 0.001003328001 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12753 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) ≤ 0.000191575124 ∧
    cc1 (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) ≤ 0.000121900531 ∧
    cc2 (rhoBar 12753 BstLean.Part154.csC) ≤ 0.000070764202 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12753 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12753 BstLean.Part154.csC * nuR (rhoBar 12753 BstLean.Part154.csC)) ≤ 0.000501648274 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250816273 : ℝ) * 0.001003328001 := by gcongr
      _ ≤ (0.000501648274 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12753 BstLean.Part154.csC) * nuR (rhoBar 12753 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003328001 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12753 BstLean.Part154.csC) * rhoBar 12753 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250816273 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250816273 / 2 + 0.399 * 0.001003328001 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191575124 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501648274 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121900531 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250816273 / 1.414213562 := by gcongr
      _ ≤ (0.000070764202 : ℝ) := by norm_num

end BstLean.Part269.N12753

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12753
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) ≤ 1.58494E-7 := by
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12753 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12753 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191575124 : ℝ) ^ 2 + 0.000121900531 ^ 2 + 3 * 0.000070764202 ^ 2 +
        2 * 0.797885 * 0.000191575124 * 0.000121900531 + 2 * 0.000191575124 * 0.000070764202 +
        4 * 0.797885 * 0.000121900531 * 0.000070764202 := by gcongr
    _ ≤ (1.58494E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12753 BstLean.Part154.csC Θ ≤ 0.002617978321 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12753 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12753 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035734080248 * 1.58494E-7 / (0.000250815885 : ℝ) := by gcongr
    _ ≤ 0.002617978321 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12753 BstLean.Part154.csC Θ ≤ 0.002904580900 + 0.000661521832 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12753 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035734080248 : ℝ) * ((2 * Θ * 0.000250816273 +
        (6863 / 10000) * 0.000250816273 * 12753 * 0.001003328001) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002904580900 + 0.000661521832 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12753 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12753 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12753 0.011 Θ ∧ gammaRatio 12753 0.011 Θ ≤ 0.000086224149 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12753 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035734080248 : ℝ) * 0.525 / ((1 - 0.011) * 12753) := by gcongr
      _ ≤ (0.000086224149 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12753 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12753 0.011 Θ) :=
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
    badAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12753 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12753 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12753 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12753 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12753 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12753 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12753 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12753 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12753 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12753 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035734080248 : ℝ) * 12753 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464742370 + 0.003279500153 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12753

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12753
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12753 BstLean.Part154.csC) (piBar (rhoBar 12753 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12753 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12753 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12753 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12753 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12753 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12753 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12753 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12753 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12753 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052373958522 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12753) ≤ 0.010575101731 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12753 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035734080248)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010575101731 + 2 * 0.737676 / 12753) := by gcongr
    _ ≤ (0.052373958522 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12753 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12753

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12753
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505955147 : ℝ) ≤ plow 12753 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12753) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693079951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374438619) : eMP 12753 0.011 xi bn ≤ 0.001183333520 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12753 : ℝ) * (1 - 0.011))) ≤ 0.000585104327 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374438619 / (12753 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585104327 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585104327 : ℝ) + 3.141593 * 0.052693079951 / (12753 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183333520 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693079951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374438619) : PiBarMP 12753 12 0.011 xi bn ≤ 0.160912116319 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12753 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037073422003 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.306353337645 : ℝ) ≤ √((12753 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.929181348312 : ℝ) ≤ √(12753 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12753) ≤ 0.123372967877 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037073422003 + 0.052693079951 * 1.772454 / (2 * (112.306353337645 : ℝ))) * (1 + 0.001183333520) +
        8 / (12753 * 112.929181348312) + 0.123372967877 := by gcongr
    _ ≤ (0.160912116319 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693079951)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374438619) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281923691589) :
    parallelOracle 12753 0.011 xi bn cd ≤ 0.161898300196 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12753 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12753 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505955147 : ℝ) ≤ plow 12753 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.929181348312 : ℝ) ≤ √(12753 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281923691589 : ℝ) / (2 * 0.560505955147 * 112.929181348312)) * 0.160912116319 +
        0.281923691589 ^ 2 / (2 * 0.560505955147 * 112.929181348312) := by gcongr
    _ ≤ (0.161898300196 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052693079951) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374438619)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281923691589) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12753 12753 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505955147 : ℝ) ≤ plow 12753 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.929181348312 : ℝ) ≤ √(12753 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12753 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12753 Θ 1.22 ≤ 0.011742762006 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.929181348312 := by gcongr <;> linarith
      _ ≤ (0.011742762006 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12753 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12753 12753 0.011 ≤ 0.008464481921 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12753 12753 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12753 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12753 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12753 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12753 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161898300196 + 0.011742762006 + (0.008464481921 : ℝ) *
        (1 + 2 * (0.281923691589 + 0.011742762006) / (0.560505955147 * 112.929181348312))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12753]

end BstLean.Part269.N12753

/-! The original eight local profiles supply actual 12753 moment certificates. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12753 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052693079951 ∧
    0 ≤ bN 12753 BstLean.Part154.csC (groupTheta g) ∧ bN 12753 BstLean.Part154.csC (groupTheta g) ≤ 0.001374438619 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12753 12753 0.011
      (momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12753 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12753 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12753 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229549733067 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12753 0.011
      (momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12753 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12753
/-! The actual computed-centre upper energy formula at 12753. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12753

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12753)
open BstLean.Part268 (cell12753)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085337188214
  | 2 => 0.086277158894
  | 3 => 0.087214869304
  | 4 => 0.088151645000
  | 5 => 0.089089092303
  | 6 => 0.090029140389
  | 7 => 0.090974087405
  | 8 => 0.091926650677
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12753 12753 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12753 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12753

/-! Actual upper energy certificates on all 43 source endpoints at 12753. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12753)
open BstLean.Part268 (cell12753)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12753 (gMinus 12753) (1 - (cell12753 i).lower) ≤ 1 ∧
    energyUpper 12753 (gMinus 12753) (BstLean.Part211.gPlus 12753)
      (finiteEnergy 12753 12753 0.011) (1 - (cell12753 i).lower) ≤
      (cell12753 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨10,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨11,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨12,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨13,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨14,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨15,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨16,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨17,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨18,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨19,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨20,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨21,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨22,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨23,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨24,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨25,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨26,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨27,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨28,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨29,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨30,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨31,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨32,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨33,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨34,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨35,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨36,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨37,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨38,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨39,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨40,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨41,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨42,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨43,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨44,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨45,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨46,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨47,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨48,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨49,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨50,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨51,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12753) (by norm_num)
        (q := 1 - (cell12753 ⟨52,by decide⟩).lower)
        (by norm_num [cell12753]) (by norm_num [cell12753])
      exact ⟨E.1,E.2.trans (by norm_num [cell12753])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12753

/-! Source-cell containment and simple scalar guards at 12753. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12753)
open BstLean.Part268 (cell12753)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12753 ⟨10,by decide⟩).lower ∧ (cell12753 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12753 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12753 ⟨11,by decide⟩).lower ∧ (cell12753 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12753 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12753 ⟨12,by decide⟩).lower ∧ (cell12753 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12753 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12753 ⟨13,by decide⟩).lower ∧ (cell12753 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12753 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12753 ⟨14,by decide⟩).lower ∧ (cell12753 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12753 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12753 ⟨15,by decide⟩).lower ∧ (cell12753 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12753 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12753 ⟨16,by decide⟩).lower ∧ (cell12753 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12753 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12753 ⟨17,by decide⟩).lower ∧ (cell12753 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12753 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12753 ⟨18,by decide⟩).lower ∧ (cell12753 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12753 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12753 ⟨19,by decide⟩).lower ∧ (cell12753 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12753 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12753 ⟨20,by decide⟩).lower ∧ (cell12753 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12753 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12753 ⟨21,by decide⟩).lower ∧ (cell12753 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12753 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12753 ⟨22,by decide⟩).lower ∧ (cell12753 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12753 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12753 ⟨23,by decide⟩).lower ∧ (cell12753 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12753 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12753 ⟨24,by decide⟩).lower ∧ (cell12753 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12753 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12753 ⟨25,by decide⟩).lower ∧ (cell12753 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12753 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12753 ⟨26,by decide⟩).lower ∧ (cell12753 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12753 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12753 ⟨27,by decide⟩).lower ∧ (cell12753 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12753 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12753 ⟨28,by decide⟩).lower ∧ (cell12753 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12753 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12753 ⟨29,by decide⟩).lower ∧ (cell12753 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12753 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12753 ⟨30,by decide⟩).lower ∧ (cell12753 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12753 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12753 ⟨31,by decide⟩).lower ∧ (cell12753 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12753 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12753 ⟨32,by decide⟩).lower ∧ (cell12753 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12753 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12753 ⟨33,by decide⟩).lower ∧ (cell12753 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12753 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12753 ⟨34,by decide⟩).lower ∧ (cell12753 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12753 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12753 ⟨35,by decide⟩).lower ∧ (cell12753 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12753 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12753 ⟨36,by decide⟩).lower ∧ (cell12753 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12753 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12753 ⟨37,by decide⟩).lower ∧ (cell12753 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12753 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12753 ⟨38,by decide⟩).lower ∧ (cell12753 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12753 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12753 ⟨39,by decide⟩).lower ∧ (cell12753 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12753 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12753 ⟨40,by decide⟩).lower ∧ (cell12753 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12753 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12753 ⟨41,by decide⟩).lower ∧ (cell12753 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12753 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12753 ⟨42,by decide⟩).lower ∧ (cell12753 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12753 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12753 ⟨43,by decide⟩).lower ∧ (cell12753 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12753 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12753 ⟨44,by decide⟩).lower ∧ (cell12753 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12753 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12753 ⟨45,by decide⟩).lower ∧ (cell12753 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12753 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12753 ⟨46,by decide⟩).lower ∧ (cell12753 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12753 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12753 ⟨47,by decide⟩).lower ∧ (cell12753 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12753 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12753 ⟨48,by decide⟩).lower ∧ (cell12753 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12753 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12753 ⟨49,by decide⟩).lower ∧ (cell12753 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12753 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12753 ⟨50,by decide⟩).lower ∧ (cell12753 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12753 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12753 ⟨51,by decide⟩).lower ∧ (cell12753 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12753 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12753 ⟨52,by decide⟩).lower ∧ (cell12753 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12753 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12753 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12753 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12753,cell12753,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12753 i).lower ∧
    (cell12753 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12753 i).upper ≤ (0.532 : ℝ) ∧
    (cell12753 i).centre ≤ (0.1 : ℝ) ∧ (cell12753 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12753 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12753 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12753

/-! The local source numeric instances at 12753 have no network premises. -/
namespace BstLean.Part269.N12753
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12753)
open BstLean.Part268 (cell12753)

noncomputable def sourceNumerics12753 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12753 (cell12753 i)
      scalarRow12753.M scalarRow12753.H scalarRow12753.xi := by
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
    energy_allowance := scalarRow12753.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12753]
    centre_nonneg := (scalarRow12753.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12753])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12753
/-! Actual 12754 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12754 ≤ (1.035732667027 : ℝ) := by
  have hr : (112.933608815091 : ℝ) ≤ √(12754 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.933608815091 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12754 12754 (11 / 1000) ≤
    (0.008464150075 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12754) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.933608815091 : ℝ) ≤ √(12754 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12754)
  have hdiv : K / √(12754 : ℝ) ≤ K / 112.933608815091 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.933608815091 ≤ (0.008464150075 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12754.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12754 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12754 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12754 := gPlus_lower 12754
end BstLean.Part269.N12754

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12754
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035732667026 : ℝ) ≤ wn 12754 := by
  have hn : √(12754 : ℝ) ≤ 112.933608815092 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12754 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.933608815092 ≤ 2 / √(12754 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250795877 : ℝ) ≤ rhoBar 12754 BstLean.Part154.csC ∧
    rhoBar 12754 BstLean.Part154.csC ≤ 0.000250796265 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035732667026 : ℝ) / (1.295212 * 12754) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035732667027 : ℝ) / (1.29521 * 12754) := by gcongr
      _ ≤ (0.000250796265 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12754 BstLean.Part154.csC) ≤ 0.001003247959 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12754 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) ≤ 0.000191559841 ∧
    cc1 (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) ≤ 0.000121890806 ∧
    cc2 (rhoBar 12754 BstLean.Part154.csC) ≤ 0.000070758557 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12754 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12754 BstLean.Part154.csC * nuR (rhoBar 12754 BstLean.Part154.csC)) ≤ 0.000501608255 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250796265 : ℝ) * 0.001003247959 := by gcongr
      _ ≤ (0.000501608255 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12754 BstLean.Part154.csC) * nuR (rhoBar 12754 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003247959 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12754 BstLean.Part154.csC) * rhoBar 12754 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250796265 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250796265 / 2 + 0.399 * 0.001003247959 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191559841 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501608255 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121890806 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250796265 / 1.414213562 := by gcongr
      _ ≤ (0.000070758557 : ℝ) := by norm_num

end BstLean.Part269.N12754

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12754
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) ≤ 1.58469E-7 := by
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12754 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12754 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191559841 : ℝ) ^ 2 + 0.000121890806 ^ 2 + 3 * 0.000070758557 ^ 2 +
        2 * 0.797885 * 0.000191559841 * 0.000121890806 + 2 * 0.000191559841 * 0.000070758557 +
        4 * 0.797885 * 0.000121890806 * 0.000070758557 := by gcongr
    _ ≤ (1.58469E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12754 BstLean.Part154.csC Θ ≤ 0.002617770627 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12754 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12754 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035732667027 * 1.58469E-7 / (0.000250795877 : ℝ) := by gcongr
    _ ≤ 0.002617770627 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12754 BstLean.Part154.csC Θ ≤ 0.002904341256 + 0.000661468159 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12754 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035732667027 : ℝ) * ((2 * Θ * 0.000250796265 +
        (6863 / 10000) * 0.000250796265 * 12754 * 0.001003247959) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002904341256 + 0.000661468159 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12754 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12754 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12754 0.011 Θ ∧ gammaRatio 12754 0.011 Θ ≤ 0.000086217271 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12754 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035732667027 : ℝ) * 0.525 / ((1 - 0.011) * 12754) := by gcongr
      _ ≤ (0.000086217271 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12754 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12754 0.011 Θ) :=
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
    badAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12754 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12754 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12754 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12754 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12754 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12754 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12754 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12754 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12754 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12754 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035732667027 : ℝ) * 12754 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464502726 + 0.003279238786 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12754

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12754
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12754 BstLean.Part154.csC) (piBar (rhoBar 12754 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12754 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12754 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12754 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12754 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12754 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12754 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12754 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12754 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12754 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052371883027 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12754) ≤ 0.010574687143 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12754 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035732667027)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010574687143 + 2 * 0.737676 / 12754) := by gcongr
    _ ≤ (0.052371883027 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12754 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12754

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12754
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560505999992 : ℝ) ≤ plow 12754 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12754) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692703089)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374329580) : eMP 12754 0.011 xi bn ≤ 0.001183240103 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12754 : ℝ) * (1 - 0.011))) ≤ 0.000585058180 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374329580 / (12754 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585058180 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585058180 : ℝ) + 3.141593 * 0.052692703089 / (12754 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183240103 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692703089)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374329580) : PiBarMP 12754 12 0.011 xi bn ≤ 0.160905783780 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12754 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037071951392 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.310756386020 : ℝ) ≤ √((12754 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.933608815091 : ℝ) ≤ √(12754 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12754) ≤ 0.123368131143 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037071951392 + 0.052692703089 * 1.772454 / (2 * (112.310756386020 : ℝ))) * (1 + 0.001183240103) +
        8 / (12754 * 112.933608815091) + 0.123368131143 := by gcongr
    _ ≤ (0.160905783780 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692703089)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374329580) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281920795221) :
    parallelOracle 12754 0.011 xi bn cd ≤ 0.161891898233 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12754 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12754 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560505999992 : ℝ) ≤ plow 12754 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.933608815091 : ℝ) ≤ √(12754 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281920795221 : ℝ) / (2 * 0.560505999992 * 112.933608815091)) * 0.160905783780 +
        0.281920795221 ^ 2 / (2 * 0.560505999992 * 112.933608815091) := by gcongr
    _ ≤ (0.161891898233 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692703089) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374329580)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281920795221) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12754 12754 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560505999992 : ℝ) ≤ plow 12754 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.933608815091 : ℝ) ≤ √(12754 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12754 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12754 Θ 1.22 ≤ 0.011742301640 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.933608815091 := by gcongr <;> linarith
      _ ≤ (0.011742301640 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12754 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12754 12754 0.011 ≤ 0.008464150075 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12754 12754 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12754 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12754 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12754 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12754 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161891898233 + 0.011742301640 + (0.008464150075 : ℝ) *
        (1 + 2 * (0.281920795221 + 0.011742301640) / (0.560505999992 * 112.933608815091))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12754]

end BstLean.Part269.N12754

/-! The original eight local profiles supply actual 12754 moment certificates. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12754 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052692703089 ∧
    0 ≤ bN 12754 BstLean.Part154.csC (groupTheta g) ∧ bN 12754 BstLean.Part154.csC (groupTheta g) ≤ 0.001374329580 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12754 12754 0.011
      (momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12754 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12754 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12754 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229548912194 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12754 0.011
      (momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12754 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12754
/-! The actual computed-centre upper energy formula at 12754. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12754

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12754)
open BstLean.Part268 (cell12754)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085334328374
  | 2 => 0.086274247776
  | 3 => 0.087211899631
  | 4 => 0.088148607807
  | 5 => 0.089085976633
  | 6 => 0.090025932954
  | 7 => 0.090970772211
  | 8 => 0.091923208599
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12754 12754 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12754 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12754

/-! Actual upper energy certificates on all 43 source endpoints at 12754. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12754)
open BstLean.Part268 (cell12754)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12754 (gMinus 12754) (1 - (cell12754 i).lower) ≤ 1 ∧
    energyUpper 12754 (gMinus 12754) (BstLean.Part211.gPlus 12754)
      (finiteEnergy 12754 12754 0.011) (1 - (cell12754 i).lower) ≤
      (cell12754 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨10,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨11,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨12,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨13,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨14,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨15,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨16,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨17,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨18,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨19,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨20,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨21,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨22,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨23,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨24,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨25,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨26,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨27,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨28,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨29,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨30,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨31,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨32,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨33,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨34,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨35,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨36,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨37,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨38,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨39,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨40,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨41,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨42,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨43,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨44,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨45,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨46,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨47,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨48,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨49,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨50,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨51,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12754) (by norm_num)
        (q := 1 - (cell12754 ⟨52,by decide⟩).lower)
        (by norm_num [cell12754]) (by norm_num [cell12754])
      exact ⟨E.1,E.2.trans (by norm_num [cell12754])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12754

/-! Source-cell containment and simple scalar guards at 12754. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12754)
open BstLean.Part268 (cell12754)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12754 ⟨10,by decide⟩).lower ∧ (cell12754 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12754 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12754 ⟨11,by decide⟩).lower ∧ (cell12754 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12754 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12754 ⟨12,by decide⟩).lower ∧ (cell12754 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12754 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12754 ⟨13,by decide⟩).lower ∧ (cell12754 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12754 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12754 ⟨14,by decide⟩).lower ∧ (cell12754 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12754 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12754 ⟨15,by decide⟩).lower ∧ (cell12754 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12754 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12754 ⟨16,by decide⟩).lower ∧ (cell12754 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12754 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12754 ⟨17,by decide⟩).lower ∧ (cell12754 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12754 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12754 ⟨18,by decide⟩).lower ∧ (cell12754 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12754 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12754 ⟨19,by decide⟩).lower ∧ (cell12754 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12754 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12754 ⟨20,by decide⟩).lower ∧ (cell12754 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12754 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12754 ⟨21,by decide⟩).lower ∧ (cell12754 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12754 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12754 ⟨22,by decide⟩).lower ∧ (cell12754 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12754 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12754 ⟨23,by decide⟩).lower ∧ (cell12754 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12754 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12754 ⟨24,by decide⟩).lower ∧ (cell12754 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12754 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12754 ⟨25,by decide⟩).lower ∧ (cell12754 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12754 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12754 ⟨26,by decide⟩).lower ∧ (cell12754 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12754 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12754 ⟨27,by decide⟩).lower ∧ (cell12754 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12754 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12754 ⟨28,by decide⟩).lower ∧ (cell12754 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12754 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12754 ⟨29,by decide⟩).lower ∧ (cell12754 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12754 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12754 ⟨30,by decide⟩).lower ∧ (cell12754 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12754 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12754 ⟨31,by decide⟩).lower ∧ (cell12754 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12754 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12754 ⟨32,by decide⟩).lower ∧ (cell12754 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12754 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12754 ⟨33,by decide⟩).lower ∧ (cell12754 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12754 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12754 ⟨34,by decide⟩).lower ∧ (cell12754 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12754 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12754 ⟨35,by decide⟩).lower ∧ (cell12754 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12754 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12754 ⟨36,by decide⟩).lower ∧ (cell12754 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12754 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12754 ⟨37,by decide⟩).lower ∧ (cell12754 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12754 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12754 ⟨38,by decide⟩).lower ∧ (cell12754 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12754 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12754 ⟨39,by decide⟩).lower ∧ (cell12754 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12754 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12754 ⟨40,by decide⟩).lower ∧ (cell12754 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12754 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12754 ⟨41,by decide⟩).lower ∧ (cell12754 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12754 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12754 ⟨42,by decide⟩).lower ∧ (cell12754 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12754 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12754 ⟨43,by decide⟩).lower ∧ (cell12754 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12754 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12754 ⟨44,by decide⟩).lower ∧ (cell12754 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12754 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12754 ⟨45,by decide⟩).lower ∧ (cell12754 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12754 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12754 ⟨46,by decide⟩).lower ∧ (cell12754 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12754 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12754 ⟨47,by decide⟩).lower ∧ (cell12754 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12754 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12754 ⟨48,by decide⟩).lower ∧ (cell12754 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12754 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12754 ⟨49,by decide⟩).lower ∧ (cell12754 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12754 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12754 ⟨50,by decide⟩).lower ∧ (cell12754 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12754 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12754 ⟨51,by decide⟩).lower ∧ (cell12754 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12754 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12754 ⟨52,by decide⟩).lower ∧ (cell12754 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12754 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12754 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12754 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12754,cell12754,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12754 i).lower ∧
    (cell12754 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12754 i).upper ≤ (0.532 : ℝ) ∧
    (cell12754 i).centre ≤ (0.1 : ℝ) ∧ (cell12754 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12754 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12754 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12754

/-! The local source numeric instances at 12754 have no network premises. -/
namespace BstLean.Part269.N12754
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12754)
open BstLean.Part268 (cell12754)

noncomputable def sourceNumerics12754 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12754 (cell12754 i)
      scalarRow12754.M scalarRow12754.H scalarRow12754.xi := by
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
    energy_allowance := scalarRow12754.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12754]
    centre_nonneg := (scalarRow12754.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12754])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12754
/-! Actual 12755 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12755 ≤ (1.035731253974 : ℝ) := by
  have hr : (112.938036108301 : ℝ) ≤ √(12755 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.938036108301 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12755 12755 (11 / 1000) ≤
    (0.008463818269 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12755) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.938036108301 : ℝ) ≤ √(12755 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12755)
  have hdiv : K / √(12755 : ℝ) ≤ K / 112.938036108301 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.938036108301 ≤ (0.008463818269 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12755.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12755 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12755 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12755 := gPlus_lower 12755
end BstLean.Part269.N12755

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12755
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035731253973 : ℝ) ≤ wn 12755 := by
  have hn : √(12755 : ℝ) ≤ 112.938036108302 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12755 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.938036108302 ≤ 2 / √(12755 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250775872 : ℝ) ≤ rhoBar 12755 BstLean.Part154.csC ∧
    rhoBar 12755 BstLean.Part154.csC ≤ 0.000250776260 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035731253973 : ℝ) / (1.295212 * 12755) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035731253974 : ℝ) / (1.29521 * 12755) := by gcongr
      _ ≤ (0.000250776260 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12755 BstLean.Part154.csC) ≤ 0.001003167929 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12755 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) ≤ 0.000191544560 ∧
    cc1 (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) ≤ 0.000121881084 ∧
    cc2 (rhoBar 12755 BstLean.Part154.csC) ≤ 0.000070752913 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12755 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12755 BstLean.Part154.csC * nuR (rhoBar 12755 BstLean.Part154.csC)) ≤ 0.000501568243 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250776260 : ℝ) * 0.001003167929 := by gcongr
      _ ≤ (0.000501568243 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12755 BstLean.Part154.csC) * nuR (rhoBar 12755 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003167929 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12755 BstLean.Part154.csC) * rhoBar 12755 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250776260 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250776260 / 2 + 0.399 * 0.001003167929 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191544560 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501568243 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121881084 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250776260 / 1.414213562 := by gcongr
      _ ≤ (0.000070752913 : ℝ) := by norm_num

end BstLean.Part269.N12755

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12755
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) ≤ 1.58444E-7 := by
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12755 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12755 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191544560 : ℝ) ^ 2 + 0.000121881084 ^ 2 + 3 * 0.000070752913 ^ 2 +
        2 * 0.797885 * 0.000191544560 * 0.000121881084 + 2 * 0.000191544560 * 0.000070752913 +
        4 * 0.797885 * 0.000121881084 * 0.000070752913 := by gcongr
    _ ≤ (1.58444E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12755 BstLean.Part154.csC Θ ≤ 0.002617562870 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12755 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12755 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035731253974 * 1.58444E-7 / (0.000250775872 : ℝ) := by gcongr
    _ ≤ 0.002617562870 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12755 BstLean.Part154.csC Θ ≤ 0.002904101647 + 0.000661414494 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12755 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035731253974 : ℝ) * ((2 * Θ * 0.000250776260 +
        (6863 / 10000) * 0.000250776260 * 12755 * 0.001003167929) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002904101647 + 0.000661414494 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12755 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12755 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12755 0.011 Θ ∧ gammaRatio 12755 0.011 Θ ≤ 0.000086210394 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12755 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035731253974 : ℝ) * 0.525 / ((1 - 0.011) * 12755) := by gcongr
      _ ≤ (0.000086210394 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12755 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12755 0.011 Θ) :=
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
    badAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12755 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12755 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12755 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12755 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12755 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12755 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12755 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12755 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12755 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12755 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035731253974 : ℝ) * 12755 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464263117 + 0.003278977364 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12755

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12755
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12755 BstLean.Part154.csC) (piBar (rhoBar 12755 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12755 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12755 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12755 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12755 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12755 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12755 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12755 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12755 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12755 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052369807774 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12755) ≤ 0.010574272603 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12755 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035731253974)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010574272603 + 2 * 0.737676 / 12755) := by gcongr
    _ ≤ (0.052369807774 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12755 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12755

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12755
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506044829 : ℝ) ≤ plow 12755 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12755) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692326234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374220507) : eMP 12755 0.011 xi bn ≤ 0.001183146678 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12755 : ℝ) * (1 - 0.011))) ≤ 0.000585012029 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374220507 / (12755 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000585012029 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000585012029 : ℝ) + 3.141593 * 0.052692326234 / (12755 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183146678 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692326234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374220507) : PiBarMP 12755 12 0.011 xi bn ≤ 0.160899451296 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12755 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037070480264 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.315159261784 : ℝ) ≤ √((12755 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.938036108301 : ℝ) ≤ √(12755 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12755) ≤ 0.123363294979 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037070480264 + 0.052692326234 * 1.772454 / (2 * (112.315159261784 : ℝ))) * (1 + 0.001183146678) +
        8 / (12755 * 112.938036108301) + 0.123363294979 := by gcongr
    _ ≤ (0.160899451296 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692326234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374220507) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281917899106) :
    parallelOracle 12755 0.011 xi bn cd ≤ 0.161885496334 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12755 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12755 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506044829 : ℝ) ≤ plow 12755 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.938036108301 : ℝ) ≤ √(12755 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281917899106 : ℝ) / (2 * 0.560506044829 * 112.938036108301)) * 0.160899451296 +
        0.281917899106 ^ 2 / (2 * 0.560506044829 * 112.938036108301) := by gcongr
    _ ≤ (0.161885496334 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052692326234) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374220507)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281917899106) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12755 12755 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506044829 : ℝ) ≤ plow 12755 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.938036108301 : ℝ) ≤ √(12755 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12755 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12755 Θ 1.22 ≤ 0.011741841330 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.938036108301 := by gcongr <;> linarith
      _ ≤ (0.011741841330 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12755 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12755 12755 0.011 ≤ 0.008463818269 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12755 12755 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12755 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12755 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12755 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12755 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161885496334 + 0.011741841330 + (0.008463818269 : ℝ) *
        (1 + 2 * (0.281917899106 + 0.011741841330) / (0.560506044829 * 112.938036108301))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12755]

end BstLean.Part269.N12755

/-! The original eight local profiles supply actual 12755 moment certificates. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12755 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052692326234 ∧
    0 ≤ bN 12755 BstLean.Part154.csC (groupTheta g) ∧ bN 12755 BstLean.Part154.csC (groupTheta g) ≤ 0.001374220507 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12755 12755 0.011
      (momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12755 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12755 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12755 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229548091332 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12755 0.011
      (momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12755 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12755
/-! The actual computed-centre upper energy formula at 12755. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12755

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12755)
open BstLean.Part268 (cell12755)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085331469562
  | 2 => 0.086271337725
  | 3 => 0.087208931078
  | 4 => 0.088145571796
  | 5 => 0.089082862222
  | 6 => 0.090022726873
  | 7 => 0.090967458484
  | 8 => 0.091919768124
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12755 12755 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12755 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12755

/-! Actual upper energy certificates on all 43 source endpoints at 12755. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12755)
open BstLean.Part268 (cell12755)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12755 (gMinus 12755) (1 - (cell12755 i).lower) ≤ 1 ∧
    energyUpper 12755 (gMinus 12755) (BstLean.Part211.gPlus 12755)
      (finiteEnergy 12755 12755 0.011) (1 - (cell12755 i).lower) ≤
      (cell12755 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨10,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨11,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨12,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨13,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨14,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨15,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨16,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨17,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨18,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨19,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨20,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨21,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨22,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨23,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨24,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨25,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨26,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨27,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨28,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨29,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨30,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨31,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨32,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨33,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨34,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨35,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨36,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨37,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨38,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨39,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨40,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨41,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨42,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨43,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨44,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨45,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨46,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨47,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨48,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨49,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨50,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨51,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12755) (by norm_num)
        (q := 1 - (cell12755 ⟨52,by decide⟩).lower)
        (by norm_num [cell12755]) (by norm_num [cell12755])
      exact ⟨E.1,E.2.trans (by norm_num [cell12755])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12755

/-! Source-cell containment and simple scalar guards at 12755. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12755)
open BstLean.Part268 (cell12755)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12755 ⟨10,by decide⟩).lower ∧ (cell12755 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12755 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12755 ⟨11,by decide⟩).lower ∧ (cell12755 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12755 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12755 ⟨12,by decide⟩).lower ∧ (cell12755 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12755 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12755 ⟨13,by decide⟩).lower ∧ (cell12755 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12755 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12755 ⟨14,by decide⟩).lower ∧ (cell12755 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12755 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12755 ⟨15,by decide⟩).lower ∧ (cell12755 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12755 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12755 ⟨16,by decide⟩).lower ∧ (cell12755 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12755 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12755 ⟨17,by decide⟩).lower ∧ (cell12755 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12755 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12755 ⟨18,by decide⟩).lower ∧ (cell12755 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12755 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12755 ⟨19,by decide⟩).lower ∧ (cell12755 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12755 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12755 ⟨20,by decide⟩).lower ∧ (cell12755 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12755 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12755 ⟨21,by decide⟩).lower ∧ (cell12755 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12755 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12755 ⟨22,by decide⟩).lower ∧ (cell12755 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12755 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12755 ⟨23,by decide⟩).lower ∧ (cell12755 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12755 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12755 ⟨24,by decide⟩).lower ∧ (cell12755 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12755 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12755 ⟨25,by decide⟩).lower ∧ (cell12755 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12755 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12755 ⟨26,by decide⟩).lower ∧ (cell12755 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12755 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12755 ⟨27,by decide⟩).lower ∧ (cell12755 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12755 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12755 ⟨28,by decide⟩).lower ∧ (cell12755 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12755 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12755 ⟨29,by decide⟩).lower ∧ (cell12755 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12755 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12755 ⟨30,by decide⟩).lower ∧ (cell12755 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12755 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12755 ⟨31,by decide⟩).lower ∧ (cell12755 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12755 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12755 ⟨32,by decide⟩).lower ∧ (cell12755 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12755 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12755 ⟨33,by decide⟩).lower ∧ (cell12755 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12755 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12755 ⟨34,by decide⟩).lower ∧ (cell12755 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12755 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12755 ⟨35,by decide⟩).lower ∧ (cell12755 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12755 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12755 ⟨36,by decide⟩).lower ∧ (cell12755 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12755 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12755 ⟨37,by decide⟩).lower ∧ (cell12755 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12755 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12755 ⟨38,by decide⟩).lower ∧ (cell12755 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12755 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12755 ⟨39,by decide⟩).lower ∧ (cell12755 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12755 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12755 ⟨40,by decide⟩).lower ∧ (cell12755 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12755 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12755 ⟨41,by decide⟩).lower ∧ (cell12755 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12755 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12755 ⟨42,by decide⟩).lower ∧ (cell12755 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12755 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12755 ⟨43,by decide⟩).lower ∧ (cell12755 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12755 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12755 ⟨44,by decide⟩).lower ∧ (cell12755 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12755 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12755 ⟨45,by decide⟩).lower ∧ (cell12755 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12755 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12755 ⟨46,by decide⟩).lower ∧ (cell12755 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12755 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12755 ⟨47,by decide⟩).lower ∧ (cell12755 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12755 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12755 ⟨48,by decide⟩).lower ∧ (cell12755 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12755 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12755 ⟨49,by decide⟩).lower ∧ (cell12755 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12755 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12755 ⟨50,by decide⟩).lower ∧ (cell12755 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12755 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12755 ⟨51,by decide⟩).lower ∧ (cell12755 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12755 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12755 ⟨52,by decide⟩).lower ∧ (cell12755 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12755 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12755 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12755 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12755,cell12755,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12755 i).lower ∧
    (cell12755 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12755 i).upper ≤ (0.532 : ℝ) ∧
    (cell12755 i).centre ≤ (0.1 : ℝ) ∧ (cell12755 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12755 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12755 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12755

/-! The local source numeric instances at 12755 have no network premises. -/
namespace BstLean.Part269.N12755
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12755)
open BstLean.Part268 (cell12755)

noncomputable def sourceNumerics12755 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12755 (cell12755 i)
      scalarRow12755.M scalarRow12755.H scalarRow12755.xi := by
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
    energy_allowance := scalarRow12755.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12755]
    centre_nonneg := (scalarRow12755.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12755])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12755
/-! Actual 12756 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12756 ≤ (1.035729841088 : ℝ) := by
  have hr : (112.942463227963 : ℝ) ≤ √(12756 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.942463227963 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12756 12756 (11 / 1000) ≤
    (0.008463486502 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12756) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.942463227963 : ℝ) ≤ √(12756 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12756)
  have hdiv : K / √(12756 : ℝ) ≤ K / 112.942463227963 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.942463227963 ≤ (0.008463486502 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12756.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12756 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12756 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12756 := gPlus_lower 12756
end BstLean.Part269.N12756

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12756
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035729841087 : ℝ) ≤ wn 12756 := by
  have hn : √(12756 : ℝ) ≤ 112.942463227964 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12756 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.942463227964 ≤ 2 / √(12756 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250755871 : ℝ) ≤ rhoBar 12756 BstLean.Part154.csC ∧
    rhoBar 12756 BstLean.Part154.csC ≤ 0.000250756259 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035729841087 : ℝ) / (1.295212 * 12756) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035729841088 : ℝ) / (1.29521 * 12756) := by gcongr
      _ ≤ (0.000250756259 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12756 BstLean.Part154.csC) ≤ 0.001003087915 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12756 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) ≤ 0.000191529282 ∧
    cc1 (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) ≤ 0.000121871362 ∧
    cc2 (rhoBar 12756 BstLean.Part154.csC) ≤ 0.000070747270 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12756 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12756 BstLean.Part154.csC * nuR (rhoBar 12756 BstLean.Part154.csC)) ≤ 0.000501528238 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250756259 : ℝ) * 0.001003087915 := by gcongr
      _ ≤ (0.000501528238 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12756 BstLean.Part154.csC) * nuR (rhoBar 12756 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003087915 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12756 BstLean.Part154.csC) * rhoBar 12756 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250756259 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250756259 / 2 + 0.399 * 0.001003087915 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191529282 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501528238 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121871362 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250756259 / 1.414213562 := by gcongr
      _ ≤ (0.000070747270 : ℝ) := by norm_num

end BstLean.Part269.N12756

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12756
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) ≤ 1.58418E-7 := by
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12756 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12756 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191529282 : ℝ) ^ 2 + 0.000121871362 ^ 2 + 3 * 0.000070747270 ^ 2 +
        2 * 0.797885 * 0.000191529282 * 0.000121871362 + 2 * 0.000191529282 * 0.000070747270 +
        4 * 0.797885 * 0.000121871362 * 0.000070747270 := by gcongr
    _ ≤ (1.58418E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12756 BstLean.Part154.csC Θ ≤ 0.002617338519 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12756 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12756 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035729841088 * 1.58418E-7 / (0.000250755871 : ℝ) := by gcongr
    _ ≤ 0.002617338519 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12756 BstLean.Part154.csC Θ ≤ 0.002903862096 + 0.000661360840 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12756 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035729841088 : ℝ) * ((2 * Θ * 0.000250756259 +
        (6863 / 10000) * 0.000250756259 * 12756 * 0.001003087915) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002903862096 + 0.000661360840 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12756 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12756 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12756 0.011 Θ ∧ gammaRatio 12756 0.011 Θ ≤ 0.000086203518 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12756 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035729841088 : ℝ) * 0.525 / ((1 - 0.011) * 12756) := by gcongr
      _ ≤ (0.000086203518 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12756 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12756 0.011 Θ) :=
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
    badAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12756 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12756 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12756 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12756 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12756 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12756 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12756 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12756 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12756 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12756 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035729841088 : ℝ) * 12756 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003464023566 + 0.003278699359 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12756

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12756
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12756 BstLean.Part154.csC) (piBar (rhoBar 12756 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12756 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12756 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12756 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12756 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12756 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12756 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12756 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12756 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12756 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052367732773 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12756) ≤ 0.010573858113 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12756 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035729841088)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010573858113 + 2 * 0.737676 / 12756) := by gcongr
    _ ≤ (0.052367732773 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12756 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12756

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12756
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506089659 : ℝ) ≤ plow 12756 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12756) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691940730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374102723) : eMP 12756 0.011 xi bn ≤ 0.001183049549 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12756 : ℝ) * (1 - 0.011))) ≤ 0.000584964027 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001374102723 / (12756 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584964027 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584964027 : ℝ) + 3.141593 * 0.052691940730 / (12756 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001183049549 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691940730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374102723) : PiBarMP 12756 12 0.011 xi bn ≤ 0.160893001483 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12756 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037068891581 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.319561964957 : ℝ) ≤ √((12756 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.942463227963 : ℝ) ≤ √(12756 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12756) ≤ 0.123358459384 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037068891581 + 0.052691940730 * 1.772454 / (2 * (112.319561964957 : ℝ))) * (1 + 0.001183049549) +
        8 / (12756 * 112.942463227963) + 0.123358459384 := by gcongr
    _ ≤ (0.160893001483 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691940730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374102723) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281914984402) :
    parallelOracle 12756 0.011 xi bn cd ≤ 0.161878976745 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12756 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12756 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506089659 : ℝ) ≤ plow 12756 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.942463227963 : ℝ) ≤ √(12756 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281914984402 : ℝ) / (2 * 0.560506089659 * 112.942463227963)) * 0.160893001483 +
        0.281914984402 ^ 2 / (2 * 0.560506089659 * 112.942463227963) := by gcongr
    _ ≤ (0.161878976745 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691940730) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001374102723)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281914984402) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12756 12756 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506089659 : ℝ) ≤ plow 12756 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.942463227963 : ℝ) ≤ √(12756 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12756 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12756 Θ 1.22 ≤ 0.011741381073 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.942463227963 := by gcongr <;> linarith
      _ ≤ (0.011741381073 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12756 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12756 12756 0.011 ≤ 0.008463486502 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12756 12756 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12756 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12756 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12756 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12756 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161878976745 + 0.011741381073 + (0.008463486502 : ℝ) *
        (1 + 2 * (0.281914984402 + 0.011741381073) / (0.560506089659 * 112.942463227963))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12756]

end BstLean.Part269.N12756

/-! The original eight local profiles supply actual 12756 moment certificates. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12756 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052691940730 ∧
    0 ≤ bN 12756 BstLean.Part154.csC (groupTheta g) ∧ bN 12756 BstLean.Part154.csC (groupTheta g) ≤ 0.001374102723 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12756 12756 0.011
      (momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12756 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12756 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12756 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229547251629 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12756 0.011
      (momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12756 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12756
/-! The actual computed-centre upper energy formula at 12756. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12756

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12756)
open BstLean.Part268 (cell12756)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085328611775
  | 2 => 0.086268428742
  | 3 => 0.087205963643
  | 4 => 0.088142536967
  | 5 => 0.089079749069
  | 6 => 0.090019522143
  | 7 => 0.090964146222
  | 8 => 0.091916329251
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12756 12756 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12756 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12756

/-! Actual upper energy certificates on all 43 source endpoints at 12756. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12756)
open BstLean.Part268 (cell12756)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12756 (gMinus 12756) (1 - (cell12756 i).lower) ≤ 1 ∧
    energyUpper 12756 (gMinus 12756) (BstLean.Part211.gPlus 12756)
      (finiteEnergy 12756 12756 0.011) (1 - (cell12756 i).lower) ≤
      (cell12756 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨10,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨11,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨12,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨13,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨14,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨15,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨16,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨17,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨18,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨19,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨20,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨21,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨22,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨23,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨24,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨25,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨26,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨27,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨28,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨29,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨30,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨31,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨32,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨33,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨34,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨35,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨36,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨37,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨38,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨39,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨40,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨41,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨42,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨43,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨44,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨45,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨46,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨47,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨48,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨49,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨50,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨51,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12756) (by norm_num)
        (q := 1 - (cell12756 ⟨52,by decide⟩).lower)
        (by norm_num [cell12756]) (by norm_num [cell12756])
      exact ⟨E.1,E.2.trans (by norm_num [cell12756])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12756

/-! Source-cell containment and simple scalar guards at 12756. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12756)
open BstLean.Part268 (cell12756)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12756 ⟨10,by decide⟩).lower ∧ (cell12756 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12756 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12756 ⟨11,by decide⟩).lower ∧ (cell12756 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12756 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12756 ⟨12,by decide⟩).lower ∧ (cell12756 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12756 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12756 ⟨13,by decide⟩).lower ∧ (cell12756 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12756 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12756 ⟨14,by decide⟩).lower ∧ (cell12756 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12756 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12756 ⟨15,by decide⟩).lower ∧ (cell12756 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12756 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12756 ⟨16,by decide⟩).lower ∧ (cell12756 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12756 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12756 ⟨17,by decide⟩).lower ∧ (cell12756 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12756 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12756 ⟨18,by decide⟩).lower ∧ (cell12756 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12756 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12756 ⟨19,by decide⟩).lower ∧ (cell12756 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12756 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12756 ⟨20,by decide⟩).lower ∧ (cell12756 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12756 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12756 ⟨21,by decide⟩).lower ∧ (cell12756 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12756 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12756 ⟨22,by decide⟩).lower ∧ (cell12756 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12756 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12756 ⟨23,by decide⟩).lower ∧ (cell12756 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12756 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12756 ⟨24,by decide⟩).lower ∧ (cell12756 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12756 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12756 ⟨25,by decide⟩).lower ∧ (cell12756 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12756 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12756 ⟨26,by decide⟩).lower ∧ (cell12756 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12756 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12756 ⟨27,by decide⟩).lower ∧ (cell12756 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12756 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12756 ⟨28,by decide⟩).lower ∧ (cell12756 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12756 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12756 ⟨29,by decide⟩).lower ∧ (cell12756 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12756 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12756 ⟨30,by decide⟩).lower ∧ (cell12756 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12756 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12756 ⟨31,by decide⟩).lower ∧ (cell12756 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12756 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12756 ⟨32,by decide⟩).lower ∧ (cell12756 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12756 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12756 ⟨33,by decide⟩).lower ∧ (cell12756 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12756 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12756 ⟨34,by decide⟩).lower ∧ (cell12756 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12756 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12756 ⟨35,by decide⟩).lower ∧ (cell12756 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12756 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12756 ⟨36,by decide⟩).lower ∧ (cell12756 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12756 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12756 ⟨37,by decide⟩).lower ∧ (cell12756 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12756 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12756 ⟨38,by decide⟩).lower ∧ (cell12756 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12756 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12756 ⟨39,by decide⟩).lower ∧ (cell12756 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12756 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12756 ⟨40,by decide⟩).lower ∧ (cell12756 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12756 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12756 ⟨41,by decide⟩).lower ∧ (cell12756 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12756 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12756 ⟨42,by decide⟩).lower ∧ (cell12756 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12756 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12756 ⟨43,by decide⟩).lower ∧ (cell12756 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12756 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12756 ⟨44,by decide⟩).lower ∧ (cell12756 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12756 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12756 ⟨45,by decide⟩).lower ∧ (cell12756 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12756 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12756 ⟨46,by decide⟩).lower ∧ (cell12756 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12756 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12756 ⟨47,by decide⟩).lower ∧ (cell12756 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12756 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12756 ⟨48,by decide⟩).lower ∧ (cell12756 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12756 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12756 ⟨49,by decide⟩).lower ∧ (cell12756 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12756 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12756 ⟨50,by decide⟩).lower ∧ (cell12756 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12756 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12756 ⟨51,by decide⟩).lower ∧ (cell12756 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12756 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12756 ⟨52,by decide⟩).lower ∧ (cell12756 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12756 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12756 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12756 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12756,cell12756,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12756 i).lower ∧
    (cell12756 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12756 i).upper ≤ (0.532 : ℝ) ∧
    (cell12756 i).centre ≤ (0.1 : ℝ) ∧ (cell12756 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12756 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12756 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12756

/-! The local source numeric instances at 12756 have no network premises. -/
namespace BstLean.Part269.N12756
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12756)
open BstLean.Part268 (cell12756)

noncomputable def sourceNumerics12756 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12756 (cell12756 i)
      scalarRow12756.M scalarRow12756.H scalarRow12756.xi := by
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
    energy_allowance := scalarRow12756.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12756]
    centre_nonneg := (scalarRow12756.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12756])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12756
/-! Actual 12757 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12757 ≤ (1.035728428369 : ℝ) := by
  have hr : (112.946890174099 : ℝ) ≤ √(12757 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.946890174099 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12757 12757 (11 / 1000) ≤
    (0.008463154773 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12757) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.946890174099 : ℝ) ≤ √(12757 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12757)
  have hdiv : K / √(12757 : ℝ) ≤ K / 112.946890174099 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.946890174099 ≤ (0.008463154773 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12757.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12757 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12757 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12757 := gPlus_lower 12757
end BstLean.Part269.N12757

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12757
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035728428368 : ℝ) ≤ wn 12757 := by
  have hn : √(12757 : ℝ) ≤ 112.946890174100 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12757 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.946890174100 ≤ 2 / √(12757 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250735872 : ℝ) ≤ rhoBar 12757 BstLean.Part154.csC ∧
    rhoBar 12757 BstLean.Part154.csC ≤ 0.000250736261 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035728428368 : ℝ) / (1.295212 * 12757) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035728428369 : ℝ) / (1.29521 * 12757) := by gcongr
      _ ≤ (0.000250736261 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12757 BstLean.Part154.csC) ≤ 0.001003007913 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12757 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) ≤ 0.000191514007 ∧
    cc1 (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) ≤ 0.000121861643 ∧
    cc2 (rhoBar 12757 BstLean.Part154.csC) ≤ 0.000070741627 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12757 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12757 BstLean.Part154.csC * nuR (rhoBar 12757 BstLean.Part154.csC)) ≤ 0.000501488240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250736261 : ℝ) * 0.001003007913 := by gcongr
      _ ≤ (0.000501488240 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12757 BstLean.Part154.csC) * nuR (rhoBar 12757 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001003007913 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12757 BstLean.Part154.csC) * rhoBar 12757 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250736261 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250736261 / 2 + 0.399 * 0.001003007913 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191514007 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501488240 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121861643 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250736261 / 1.414213562 := by gcongr
      _ ≤ (0.000070741627 : ℝ) := by norm_num

end BstLean.Part269.N12757

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12757
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) ≤ 1.58393E-7 := by
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12757 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12757 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191514007 : ℝ) ^ 2 + 0.000121861643 ^ 2 + 3 * 0.000070741627 ^ 2 +
        2 * 0.797885 * 0.000191514007 * 0.000121861643 + 2 * 0.000191514007 * 0.000070741627 +
        4 * 0.797885 * 0.000121861643 * 0.000070741627 := by gcongr
    _ ≤ (1.58393E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12757 BstLean.Part154.csC Θ ≤ 0.002617130635 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12757 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12757 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035728428369 * 1.58393E-7 / (0.000250735872 : ℝ) := by gcongr
    _ ≤ 0.002617130635 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12757 BstLean.Part154.csC Θ ≤ 0.002903622579 + 0.000661307194 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12757 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035728428369 : ℝ) * ((2 * Θ * 0.000250736261 +
        (6863 / 10000) * 0.000250736261 * 12757 * 0.001003007913) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002903622579 + 0.000661307194 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12757 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12757 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12757 0.011 Θ ∧ gammaRatio 12757 0.011 Θ ≤ 0.000086196643 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12757 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035728428369 : ℝ) * 0.525 / ((1 - 0.011) * 12757) := by gcongr
      _ ≤ (0.000086196643 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12757 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12757 0.011 Θ) :=
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
    badAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12757 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12757 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12757 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12757 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12757 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12757 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12757 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12757 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12757 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12757 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035728428369 : ℝ) * 12757 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003463784049 + 0.003278437829 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12757

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12757
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12757 BstLean.Part154.csC) (piBar (rhoBar 12757 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12757 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12757 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12757 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12757 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12757 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12757 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12757 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12757 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12757 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052365658014 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12757) ≤ 0.010573443671 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12757 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035728428369)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010573443671 + 2 * 0.737676 / 12757) := by gcongr
    _ ≤ (0.052365658014 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12757 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12757

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12757
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506134483 : ℝ) ≤ plow 12757 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12757) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691563910)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373993584) : eMP 12757 0.011 xi bn ≤ 0.001182956113 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12757 : ℝ) * (1 - 0.011))) ≤ 0.000584917870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373993584 / (12757 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584917870 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584917870 : ℝ) + 3.141593 * 0.052691563910 / (12757 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182956113 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691563910)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373993584) : PiBarMP 12757 12 0.011 xi bn ≤ 0.160886669128 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12757 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037067419441 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.323964495560 : ℝ) ≤ √((12757 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.946890174099 : ℝ) ≤ √(12757 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12757) ≤ 0.123353624357 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037067419441 + 0.052691563910 * 1.772454 / (2 * (112.323964495560 : ℝ))) * (1 + 0.001182956113) +
        8 / (12757 * 112.946890174099) + 0.123353624357 := by gcongr
    _ ≤ (0.160886669128 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691563910)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373993584) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281912088851) :
    parallelOracle 12757 0.011 xi bn cd ≤ 0.161872574993 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12757 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12757 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506134483 : ℝ) ≤ plow 12757 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.946890174099 : ℝ) ≤ √(12757 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281912088851 : ℝ) / (2 * 0.560506134483 * 112.946890174099)) * 0.160886669128 +
        0.281912088851 ^ 2 / (2 * 0.560506134483 * 112.946890174099) := by gcongr
    _ ≤ (0.161872574993 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691563910) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373993584)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281912088851) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12757 12757 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506134483 : ℝ) ≤ plow 12757 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.946890174099 : ℝ) ≤ √(12757 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12757 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12757 Θ 1.22 ≤ 0.011740920870 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.946890174099 := by gcongr <;> linarith
      _ ≤ (0.011740920870 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12757 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12757 12757 0.011 ≤ 0.008463154773 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12757 12757 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12757 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12757 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12757 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12757 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161872574993 + 0.011740920870 + (0.008463154773 : ℝ) *
        (1 + 2 * (0.281912088851 + 0.011740920870) / (0.560506134483 * 112.946890174099))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12757]

end BstLean.Part269.N12757

/-! The original eight local profiles supply actual 12757 moment certificates. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12757 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052691563910 ∧
    0 ≤ bN 12757 BstLean.Part154.csC (groupTheta g) ∧ bN 12757 BstLean.Part154.csC (groupTheta g) ≤ 0.001373993584 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12757 12757 0.011
      (momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12757 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12757 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12757 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229546430837 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12757 0.011
      (momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12757 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12757
/-! The actual computed-centre upper energy formula at 12757. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12757

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12757)
open BstLean.Part268 (cell12757)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085325755012
  | 2 => 0.086265520825
  | 3 => 0.087202997325
  | 4 => 0.088139503317
  | 5 => 0.089076637173
  | 6 => 0.090016318764
  | 7 => 0.090960835424
  | 8 => 0.091912891978
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12757 12757 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12757 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12757

/-! Actual upper energy certificates on all 43 source endpoints at 12757. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12757)
open BstLean.Part268 (cell12757)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12757 (gMinus 12757) (1 - (cell12757 i).lower) ≤ 1 ∧
    energyUpper 12757 (gMinus 12757) (BstLean.Part211.gPlus 12757)
      (finiteEnergy 12757 12757 0.011) (1 - (cell12757 i).lower) ≤
      (cell12757 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨10,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨11,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨12,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨13,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨14,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨15,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨16,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨17,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨18,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨19,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨20,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨21,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨22,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨23,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨24,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨25,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨26,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨27,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨28,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨29,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨30,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨31,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨32,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨33,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨34,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨35,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨36,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨37,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨38,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨39,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨40,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨41,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨42,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨43,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨44,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨45,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨46,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨47,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨48,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨49,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨50,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨51,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12757) (by norm_num)
        (q := 1 - (cell12757 ⟨52,by decide⟩).lower)
        (by norm_num [cell12757]) (by norm_num [cell12757])
      exact ⟨E.1,E.2.trans (by norm_num [cell12757])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12757

/-! Source-cell containment and simple scalar guards at 12757. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12757)
open BstLean.Part268 (cell12757)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12757 ⟨10,by decide⟩).lower ∧ (cell12757 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12757 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12757 ⟨11,by decide⟩).lower ∧ (cell12757 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12757 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12757 ⟨12,by decide⟩).lower ∧ (cell12757 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12757 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12757 ⟨13,by decide⟩).lower ∧ (cell12757 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12757 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12757 ⟨14,by decide⟩).lower ∧ (cell12757 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12757 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12757 ⟨15,by decide⟩).lower ∧ (cell12757 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12757 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12757 ⟨16,by decide⟩).lower ∧ (cell12757 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12757 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12757 ⟨17,by decide⟩).lower ∧ (cell12757 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12757 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12757 ⟨18,by decide⟩).lower ∧ (cell12757 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12757 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12757 ⟨19,by decide⟩).lower ∧ (cell12757 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12757 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12757 ⟨20,by decide⟩).lower ∧ (cell12757 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12757 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12757 ⟨21,by decide⟩).lower ∧ (cell12757 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12757 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12757 ⟨22,by decide⟩).lower ∧ (cell12757 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12757 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12757 ⟨23,by decide⟩).lower ∧ (cell12757 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12757 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12757 ⟨24,by decide⟩).lower ∧ (cell12757 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12757 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12757 ⟨25,by decide⟩).lower ∧ (cell12757 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12757 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12757 ⟨26,by decide⟩).lower ∧ (cell12757 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12757 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12757 ⟨27,by decide⟩).lower ∧ (cell12757 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12757 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12757 ⟨28,by decide⟩).lower ∧ (cell12757 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12757 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12757 ⟨29,by decide⟩).lower ∧ (cell12757 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12757 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12757 ⟨30,by decide⟩).lower ∧ (cell12757 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12757 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12757 ⟨31,by decide⟩).lower ∧ (cell12757 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12757 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12757 ⟨32,by decide⟩).lower ∧ (cell12757 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12757 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12757 ⟨33,by decide⟩).lower ∧ (cell12757 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12757 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12757 ⟨34,by decide⟩).lower ∧ (cell12757 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12757 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12757 ⟨35,by decide⟩).lower ∧ (cell12757 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12757 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12757 ⟨36,by decide⟩).lower ∧ (cell12757 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12757 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12757 ⟨37,by decide⟩).lower ∧ (cell12757 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12757 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12757 ⟨38,by decide⟩).lower ∧ (cell12757 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12757 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12757 ⟨39,by decide⟩).lower ∧ (cell12757 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12757 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12757 ⟨40,by decide⟩).lower ∧ (cell12757 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12757 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12757 ⟨41,by decide⟩).lower ∧ (cell12757 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12757 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12757 ⟨42,by decide⟩).lower ∧ (cell12757 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12757 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12757 ⟨43,by decide⟩).lower ∧ (cell12757 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12757 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12757 ⟨44,by decide⟩).lower ∧ (cell12757 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12757 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12757 ⟨45,by decide⟩).lower ∧ (cell12757 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12757 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12757 ⟨46,by decide⟩).lower ∧ (cell12757 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12757 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12757 ⟨47,by decide⟩).lower ∧ (cell12757 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12757 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12757 ⟨48,by decide⟩).lower ∧ (cell12757 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12757 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12757 ⟨49,by decide⟩).lower ∧ (cell12757 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12757 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12757 ⟨50,by decide⟩).lower ∧ (cell12757 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12757 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12757 ⟨51,by decide⟩).lower ∧ (cell12757 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12757 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12757 ⟨52,by decide⟩).lower ∧ (cell12757 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12757 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12757 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12757 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12757,cell12757,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12757 i).lower ∧
    (cell12757 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12757 i).upper ≤ (0.532 : ℝ) ∧
    (cell12757 i).centre ≤ (0.1 : ℝ) ∧ (cell12757 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12757 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12757 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12757

/-! The local source numeric instances at 12757 have no network premises. -/
namespace BstLean.Part269.N12757
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12757)
open BstLean.Part268 (cell12757)

noncomputable def sourceNumerics12757 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12757 (cell12757 i)
      scalarRow12757.M scalarRow12757.H scalarRow12757.xi := by
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
    energy_allowance := scalarRow12757.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12757]
    centre_nonneg := (scalarRow12757.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12757])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12757
/-! Actual 12758 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12758 ≤ (1.035727015817 : ℝ) := by
  have hr : (112.951316946727 : ℝ) ≤ √(12758 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.951316946727 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12758 12758 (11 / 1000) ≤
    (0.008462823084 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12758) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.951316946727 : ℝ) ≤ √(12758 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12758)
  have hdiv : K / √(12758 : ℝ) ≤ K / 112.951316946727 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.951316946727 ≤ (0.008462823084 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12758.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12758 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12758 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12758 := gPlus_lower 12758
end BstLean.Part269.N12758

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12758
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035727015816 : ℝ) ≤ wn 12758 := by
  have hn : √(12758 : ℝ) ≤ 112.951316946728 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12758 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.951316946728 ≤ 2 / √(12758 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250715877 : ℝ) ≤ rhoBar 12758 BstLean.Part154.csC ∧
    rhoBar 12758 BstLean.Part154.csC ≤ 0.000250716265 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035727015816 : ℝ) / (1.295212 * 12758) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035727015817 : ℝ) / (1.29521 * 12758) := by gcongr
      _ ≤ (0.000250716265 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12758 BstLean.Part154.csC) ≤ 0.001002927919 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12758 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) ≤ 0.000191498733 ∧
    cc1 (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) ≤ 0.000121851924 ∧
    cc2 (rhoBar 12758 BstLean.Part154.csC) ≤ 0.000070735986 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12758 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12758 BstLean.Part154.csC * nuR (rhoBar 12758 BstLean.Part154.csC)) ≤ 0.000501448245 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250716265 : ℝ) * 0.001002927919 := by gcongr
      _ ≤ (0.000501448245 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12758 BstLean.Part154.csC) * nuR (rhoBar 12758 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002927919 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12758 BstLean.Part154.csC) * rhoBar 12758 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250716265 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250716265 / 2 + 0.399 * 0.001002927919 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191498733 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501448245 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121851924 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250716265 / 1.414213562 := by gcongr
      _ ≤ (0.000070735986 : ℝ) := by norm_num

end BstLean.Part269.N12758

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12758
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) ≤ 1.58368E-7 := by
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12758 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12758 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191498733 : ℝ) ^ 2 + 0.000121851924 ^ 2 + 3 * 0.000070735986 ^ 2 +
        2 * 0.797885 * 0.000191498733 * 0.000121851924 + 2 * 0.000191498733 * 0.000070735986 +
        4 * 0.797885 * 0.000121851924 * 0.000070735986 := by gcongr
    _ ≤ (1.58368E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12758 BstLean.Part154.csC Θ ≤ 0.002616922678 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12758 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12758 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035727015817 * 1.58368E-7 / (0.000250715877 : ℝ) := by gcongr
    _ ≤ 0.002616922678 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12758 BstLean.Part154.csC Θ ≤ 0.002903383075 + 0.000661253553 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12758 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035727015817 : ℝ) * ((2 * Θ * 0.000250716265 +
        (6863 / 10000) * 0.000250716265 * 12758 * 0.001002927919) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002903383075 + 0.000661253553 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12758 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12758 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12758 0.011 Θ ∧ gammaRatio 12758 0.011 Θ ≤ 0.000086189769 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12758 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035727015817 : ℝ) * 0.525 / ((1 - 0.011) * 12758) := by gcongr
      _ ≤ (0.000086189769 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12758 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12758 0.011 Θ) :=
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
    badAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12758 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12758 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12758 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12758 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12758 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12758 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12758 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12758 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12758 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12758 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035727015817 : ℝ) * 12758 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003463544545 + 0.003278176231 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12758

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12758
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12758 BstLean.Part154.csC) (piBar (rhoBar 12758 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12758 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12758 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12758 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12758 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12758 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12758 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12758 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12758 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12758 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052363583502 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12758) ≤ 0.010573029278 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12758 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035727015817)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010573029278 + 2 * 0.737676 / 12758) := by gcongr
    _ ≤ (0.052363583502 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12758 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12758

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12758
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506179299 : ℝ) ≤ plow 12758 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12758) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691187067)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373884406) : eMP 12758 0.011 xi bn ≤ 0.001182862665 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12758 : ℝ) * (1 - 0.011))) ≤ 0.000584871707 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373884406 / (12758 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584871707 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584871707 : ℝ) + 3.141593 * 0.052691187067 / (12758 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182862665 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691187067)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373884406) : PiBarMP 12758 12 0.011 xi bn ≤ 0.160880336758 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12758 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037065946717 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.328366853613 : ℝ) ≤ √((12758 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.951316946727 : ℝ) ≤ √(12758 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12758) ≤ 0.123348789898 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037065946717 + 0.052691187067 * 1.772454 / (2 * (112.328366853613 : ℝ))) * (1 + 0.001182862665) +
        8 / (12758 * 112.951316946727) + 0.123348789898 := by gcongr
    _ ≤ (0.160880336758 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691187067)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373884406) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281909193495) :
    parallelOracle 12758 0.011 xi bn cd ≤ 0.161866173235 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12758 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12758 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506179299 : ℝ) ≤ plow 12758 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.951316946727 : ℝ) ≤ √(12758 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281909193495 : ℝ) / (2 * 0.560506179299 * 112.951316946727)) * 0.160880336758 +
        0.281909193495 ^ 2 / (2 * 0.560506179299 * 112.951316946727) := by gcongr
    _ ≤ (0.161866173235 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052691187067) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373884406)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281909193495) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12758 12758 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506179299 : ℝ) ≤ plow 12758 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.951316946727 : ℝ) ≤ √(12758 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12758 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12758 Θ 1.22 ≤ 0.011740460722 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.951316946727 := by gcongr <;> linarith
      _ ≤ (0.011740460722 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12758 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12758 12758 0.011 ≤ 0.008462823084 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12758 12758 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12758 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12758 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12758 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12758 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161866173235 + 0.011740460722 + (0.008462823084 : ℝ) *
        (1 + 2 * (0.281909193495 + 0.011740460722) / (0.560506179299 * 112.951316946727))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12758]

end BstLean.Part269.N12758

/-! The original eight local profiles supply actual 12758 moment certificates. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12758 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052691187067 ∧
    0 ≤ bN 12758 BstLean.Part154.csC (groupTheta g) ∧ bN 12758 BstLean.Part154.csC (groupTheta g) ≤ 0.001373884406 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12758 12758 0.011
      (momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12758 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12758 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12758 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229545609993 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12758 0.011
      (momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12758 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12758
/-! The actual computed-centre upper energy formula at 12758. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12758

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12758)
open BstLean.Part268 (cell12758)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085322899273
  | 2 => 0.086262613973
  | 3 => 0.087200032122
  | 4 => 0.088136470846
  | 5 => 0.089073526532
  | 6 => 0.090013116734
  | 7 => 0.090957526087
  | 8 => 0.091909456303
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12758 12758 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12758 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12758

/-! Actual upper energy certificates on all 43 source endpoints at 12758. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12758)
open BstLean.Part268 (cell12758)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12758 (gMinus 12758) (1 - (cell12758 i).lower) ≤ 1 ∧
    energyUpper 12758 (gMinus 12758) (BstLean.Part211.gPlus 12758)
      (finiteEnergy 12758 12758 0.011) (1 - (cell12758 i).lower) ≤
      (cell12758 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨10,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨11,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨12,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨13,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨14,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨15,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨16,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨17,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨18,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨19,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨20,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨21,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨22,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨23,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨24,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨25,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨26,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨27,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨28,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨29,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨30,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨31,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨32,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨33,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨34,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨35,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨36,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨37,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨38,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨39,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨40,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨41,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨42,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨43,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨44,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨45,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨46,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨47,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨48,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨49,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨50,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨51,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12758) (by norm_num)
        (q := 1 - (cell12758 ⟨52,by decide⟩).lower)
        (by norm_num [cell12758]) (by norm_num [cell12758])
      exact ⟨E.1,E.2.trans (by norm_num [cell12758])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12758

/-! Source-cell containment and simple scalar guards at 12758. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12758)
open BstLean.Part268 (cell12758)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12758 ⟨10,by decide⟩).lower ∧ (cell12758 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12758 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12758 ⟨11,by decide⟩).lower ∧ (cell12758 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12758 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12758 ⟨12,by decide⟩).lower ∧ (cell12758 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12758 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12758 ⟨13,by decide⟩).lower ∧ (cell12758 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12758 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12758 ⟨14,by decide⟩).lower ∧ (cell12758 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12758 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12758 ⟨15,by decide⟩).lower ∧ (cell12758 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12758 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12758 ⟨16,by decide⟩).lower ∧ (cell12758 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12758 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12758 ⟨17,by decide⟩).lower ∧ (cell12758 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12758 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12758 ⟨18,by decide⟩).lower ∧ (cell12758 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12758 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12758 ⟨19,by decide⟩).lower ∧ (cell12758 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12758 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12758 ⟨20,by decide⟩).lower ∧ (cell12758 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12758 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12758 ⟨21,by decide⟩).lower ∧ (cell12758 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12758 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12758 ⟨22,by decide⟩).lower ∧ (cell12758 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12758 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12758 ⟨23,by decide⟩).lower ∧ (cell12758 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12758 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12758 ⟨24,by decide⟩).lower ∧ (cell12758 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12758 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12758 ⟨25,by decide⟩).lower ∧ (cell12758 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12758 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12758 ⟨26,by decide⟩).lower ∧ (cell12758 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12758 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12758 ⟨27,by decide⟩).lower ∧ (cell12758 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12758 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12758 ⟨28,by decide⟩).lower ∧ (cell12758 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12758 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12758 ⟨29,by decide⟩).lower ∧ (cell12758 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12758 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12758 ⟨30,by decide⟩).lower ∧ (cell12758 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12758 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12758 ⟨31,by decide⟩).lower ∧ (cell12758 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12758 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12758 ⟨32,by decide⟩).lower ∧ (cell12758 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12758 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12758 ⟨33,by decide⟩).lower ∧ (cell12758 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12758 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12758 ⟨34,by decide⟩).lower ∧ (cell12758 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12758 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12758 ⟨35,by decide⟩).lower ∧ (cell12758 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12758 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12758 ⟨36,by decide⟩).lower ∧ (cell12758 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12758 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12758 ⟨37,by decide⟩).lower ∧ (cell12758 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12758 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12758 ⟨38,by decide⟩).lower ∧ (cell12758 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12758 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12758 ⟨39,by decide⟩).lower ∧ (cell12758 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12758 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12758 ⟨40,by decide⟩).lower ∧ (cell12758 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12758 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12758 ⟨41,by decide⟩).lower ∧ (cell12758 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12758 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12758 ⟨42,by decide⟩).lower ∧ (cell12758 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12758 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12758 ⟨43,by decide⟩).lower ∧ (cell12758 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12758 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12758 ⟨44,by decide⟩).lower ∧ (cell12758 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12758 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12758 ⟨45,by decide⟩).lower ∧ (cell12758 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12758 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12758 ⟨46,by decide⟩).lower ∧ (cell12758 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12758 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12758 ⟨47,by decide⟩).lower ∧ (cell12758 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12758 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12758 ⟨48,by decide⟩).lower ∧ (cell12758 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12758 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12758 ⟨49,by decide⟩).lower ∧ (cell12758 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12758 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12758 ⟨50,by decide⟩).lower ∧ (cell12758 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12758 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12758 ⟨51,by decide⟩).lower ∧ (cell12758 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12758 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12758 ⟨52,by decide⟩).lower ∧ (cell12758 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12758 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12758 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12758 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12758,cell12758,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12758 i).lower ∧
    (cell12758 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12758 i).upper ≤ (0.532 : ℝ) ∧
    (cell12758 i).centre ≤ (0.1 : ℝ) ∧ (cell12758 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12758 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12758 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12758

/-! The local source numeric instances at 12758 have no network premises. -/
namespace BstLean.Part269.N12758
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12758)
open BstLean.Part268 (cell12758)

noncomputable def sourceNumerics12758 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12758 (cell12758 i)
      scalarRow12758.M scalarRow12758.H scalarRow12758.xi := by
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
    energy_allowance := scalarRow12758.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12758]
    centre_nonneg := (scalarRow12758.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12758])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12758
/-! Actual 12759 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12759 ≤ (1.035725603432 : ℝ) := by
  have hr : (112.955743545868 : ℝ) ≤ √(12759 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.955743545868 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12759 12759 (11 / 1000) ≤
    (0.008462491434 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12759) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.955743545868 : ℝ) ≤ √(12759 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12759)
  have hdiv : K / √(12759 : ℝ) ≤ K / 112.955743545868 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.955743545868 ≤ (0.008462491434 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12759.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12759 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12759 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12759 := gPlus_lower 12759
end BstLean.Part269.N12759

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12759
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035725603431 : ℝ) ≤ wn 12759 := by
  have hn : √(12759 : ℝ) ≤ 112.955743545869 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12759 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.955743545869 ≤ 2 / √(12759 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250695885 : ℝ) ≤ rhoBar 12759 BstLean.Part154.csC ∧
    rhoBar 12759 BstLean.Part154.csC ≤ 0.000250696273 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035725603431 : ℝ) / (1.295212 * 12759) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035725603432 : ℝ) / (1.29521 * 12759) := by gcongr
      _ ≤ (0.000250696273 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12759 BstLean.Part154.csC) ≤ 0.001002847941 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12759 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) ≤ 0.000191483463 ∧
    cc1 (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) ≤ 0.000121842207 ∧
    cc2 (rhoBar 12759 BstLean.Part154.csC) ≤ 0.000070730345 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12759 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12759 BstLean.Part154.csC * nuR (rhoBar 12759 BstLean.Part154.csC)) ≤ 0.000501408259 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250696273 : ℝ) * 0.001002847941 := by gcongr
      _ ≤ (0.000501408259 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12759 BstLean.Part154.csC) * nuR (rhoBar 12759 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002847941 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12759 BstLean.Part154.csC) * rhoBar 12759 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250696273 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250696273 / 2 + 0.399 * 0.001002847941 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191483463 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501408259 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121842207 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250696273 / 1.414213562 := by gcongr
      _ ≤ (0.000070730345 : ℝ) := by norm_num

end BstLean.Part269.N12759

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12759
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) ≤ 1.58343E-7 := by
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12759 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12759 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191483463 : ℝ) ^ 2 + 0.000121842207 ^ 2 + 3 * 0.000070730345 ^ 2 +
        2 * 0.797885 * 0.000191483463 * 0.000121842207 + 2 * 0.000191483463 * 0.000070730345 +
        4 * 0.797885 * 0.000121842207 * 0.000070730345 := by gcongr
    _ ≤ (1.58343E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12759 BstLean.Part154.csC Θ ≤ 0.002616714658 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12759 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12759 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035725603432 * 1.58343E-7 / (0.000250695885 : ℝ) := by gcongr
    _ ≤ 0.002616714658 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12759 BstLean.Part154.csC Θ ≤ 0.002903143628 + 0.000661199924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12759 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035725603432 : ℝ) * ((2 * Θ * 0.000250696273 +
        (6863 / 10000) * 0.000250696273 * 12759 * 0.001002847941) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002903143628 + 0.000661199924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12759 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12759 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12759 0.011 Θ ∧ gammaRatio 12759 0.011 Θ ≤ 0.000086182896 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12759 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035725603432 : ℝ) * 0.525 / ((1 - 0.011) * 12759) := by gcongr
      _ ≤ (0.000086182896 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12759 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12759 0.011 Θ) :=
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
    badAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12759 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12759 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12759 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12759 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12759 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12759 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12759 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12759 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12759 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12759 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035725603432 : ℝ) * 12759 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003463305098 + 0.003277914582 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12759

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12759
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12759 BstLean.Part154.csC) (piBar (rhoBar 12759 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12759 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12759 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12759 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12759 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12759 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12759 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12759 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12759 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12759 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052361509237 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12759) ≤ 0.010572614934 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12759 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035725603432)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010572614934 + 2 * 0.737676 / 12759) := by gcongr
    _ ≤ (0.052361509237 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12759 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12759

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12759
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506224108 : ℝ) ≤ plow 12759 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12759) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690810254)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373775196) : eMP 12759 0.011 xi bn ≤ 0.001182769211 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12759 : ℝ) * (1 - 0.011))) ≤ 0.000584825541 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373775196 / (12759 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584825541 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584825541 : ℝ) + 3.141593 * 0.052690810254 / (12759 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182769211 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690810254)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373775196) : PiBarMP 12759 12 0.011 xi bn ≤ 0.160874004469 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12759 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037064473503 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.332769039136 : ℝ) ≤ √((12759 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.955743545868 : ℝ) ≤ √(12759 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12759) ≤ 0.123343956008 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037064473503 + 0.052690810254 * 1.772454 / (2 * (112.332769039136 : ℝ))) * (1 + 0.001182769211) +
        8 / (12759 * 112.955743545868) + 0.123343956008 := by gcongr
    _ ≤ (0.160874004469 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690810254)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373775196) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281906298449) :
    parallelOracle 12759 0.011 xi bn cd ≤ 0.161859771567 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12759 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12759 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506224108 : ℝ) ≤ plow 12759 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.955743545868 : ℝ) ≤ √(12759 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281906298449 : ℝ) / (2 * 0.560506224108 * 112.955743545868)) * 0.160874004469 +
        0.281906298449 ^ 2 / (2 * 0.560506224108 * 112.955743545868) := by gcongr
    _ ≤ (0.161859771567 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690810254) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373775196)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281906298449) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12759 12759 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506224108 : ℝ) ≤ plow 12759 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.955743545868 : ℝ) ≤ √(12759 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12759 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12759 Θ 1.22 ≤ 0.011740000627 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.955743545868 := by gcongr <;> linarith
      _ ≤ (0.011740000627 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12759 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12759 12759 0.011 ≤ 0.008462491434 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12759 12759 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12759 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12759 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12759 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12759 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161859771567 + 0.011740000627 + (0.008462491434 : ℝ) *
        (1 + 2 * (0.281906298449 + 0.011740000627) / (0.560506224108 * 112.955743545868))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12759]

end BstLean.Part269.N12759

/-! The original eight local profiles supply actual 12759 moment certificates. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12759 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052690810254 ∧
    0 ≤ bN 12759 BstLean.Part154.csC (groupTheta g) ∧ bN 12759 BstLean.Part154.csC (groupTheta g) ≤ 0.001373775196 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12759 12759 0.011
      (momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12759 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12759 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12759 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229544789212 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12759 0.011
      (momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12759 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12759
/-! The actual computed-centre upper energy formula at 12759. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12759

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12759)
open BstLean.Part268 (cell12759)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085320044557
  | 2 => 0.086259708185
  | 3 => 0.087197068035
  | 4 => 0.088133439552
  | 5 => 0.089070417146
  | 6 => 0.090009916052
  | 7 => 0.090954218212
  | 8 => 0.091906022224
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12759 12759 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12759 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12759

/-! Actual upper energy certificates on all 43 source endpoints at 12759. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12759)
open BstLean.Part268 (cell12759)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12759 (gMinus 12759) (1 - (cell12759 i).lower) ≤ 1 ∧
    energyUpper 12759 (gMinus 12759) (BstLean.Part211.gPlus 12759)
      (finiteEnergy 12759 12759 0.011) (1 - (cell12759 i).lower) ≤
      (cell12759 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨10,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨11,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨12,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨13,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨14,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨15,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨16,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨17,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨18,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨19,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨20,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨21,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨22,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨23,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨24,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨25,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨26,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨27,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨28,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨29,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨30,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨31,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨32,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨33,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨34,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨35,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨36,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨37,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨38,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨39,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨40,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨41,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨42,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨43,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨44,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨45,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨46,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨47,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨48,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨49,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨50,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨51,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12759) (by norm_num)
        (q := 1 - (cell12759 ⟨52,by decide⟩).lower)
        (by norm_num [cell12759]) (by norm_num [cell12759])
      exact ⟨E.1,E.2.trans (by norm_num [cell12759])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12759

/-! Source-cell containment and simple scalar guards at 12759. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12759)
open BstLean.Part268 (cell12759)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12759 ⟨10,by decide⟩).lower ∧ (cell12759 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12759 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12759 ⟨11,by decide⟩).lower ∧ (cell12759 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12759 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12759 ⟨12,by decide⟩).lower ∧ (cell12759 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12759 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12759 ⟨13,by decide⟩).lower ∧ (cell12759 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12759 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12759 ⟨14,by decide⟩).lower ∧ (cell12759 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12759 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12759 ⟨15,by decide⟩).lower ∧ (cell12759 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12759 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12759 ⟨16,by decide⟩).lower ∧ (cell12759 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12759 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12759 ⟨17,by decide⟩).lower ∧ (cell12759 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12759 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12759 ⟨18,by decide⟩).lower ∧ (cell12759 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12759 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12759 ⟨19,by decide⟩).lower ∧ (cell12759 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12759 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12759 ⟨20,by decide⟩).lower ∧ (cell12759 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12759 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12759 ⟨21,by decide⟩).lower ∧ (cell12759 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12759 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12759 ⟨22,by decide⟩).lower ∧ (cell12759 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12759 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12759 ⟨23,by decide⟩).lower ∧ (cell12759 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12759 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12759 ⟨24,by decide⟩).lower ∧ (cell12759 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12759 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12759 ⟨25,by decide⟩).lower ∧ (cell12759 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12759 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12759 ⟨26,by decide⟩).lower ∧ (cell12759 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12759 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12759 ⟨27,by decide⟩).lower ∧ (cell12759 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12759 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12759 ⟨28,by decide⟩).lower ∧ (cell12759 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12759 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12759 ⟨29,by decide⟩).lower ∧ (cell12759 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12759 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12759 ⟨30,by decide⟩).lower ∧ (cell12759 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12759 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12759 ⟨31,by decide⟩).lower ∧ (cell12759 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12759 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12759 ⟨32,by decide⟩).lower ∧ (cell12759 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12759 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12759 ⟨33,by decide⟩).lower ∧ (cell12759 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12759 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12759 ⟨34,by decide⟩).lower ∧ (cell12759 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12759 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12759 ⟨35,by decide⟩).lower ∧ (cell12759 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12759 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12759 ⟨36,by decide⟩).lower ∧ (cell12759 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12759 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12759 ⟨37,by decide⟩).lower ∧ (cell12759 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12759 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12759 ⟨38,by decide⟩).lower ∧ (cell12759 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12759 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12759 ⟨39,by decide⟩).lower ∧ (cell12759 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12759 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12759 ⟨40,by decide⟩).lower ∧ (cell12759 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12759 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12759 ⟨41,by decide⟩).lower ∧ (cell12759 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12759 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12759 ⟨42,by decide⟩).lower ∧ (cell12759 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12759 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12759 ⟨43,by decide⟩).lower ∧ (cell12759 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12759 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12759 ⟨44,by decide⟩).lower ∧ (cell12759 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12759 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12759 ⟨45,by decide⟩).lower ∧ (cell12759 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12759 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12759 ⟨46,by decide⟩).lower ∧ (cell12759 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12759 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12759 ⟨47,by decide⟩).lower ∧ (cell12759 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12759 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12759 ⟨48,by decide⟩).lower ∧ (cell12759 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12759 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12759 ⟨49,by decide⟩).lower ∧ (cell12759 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12759 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12759 ⟨50,by decide⟩).lower ∧ (cell12759 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12759 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12759 ⟨51,by decide⟩).lower ∧ (cell12759 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12759 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12759 ⟨52,by decide⟩).lower ∧ (cell12759 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12759 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12759 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12759 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12759,cell12759,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12759 i).lower ∧
    (cell12759 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12759 i).upper ≤ (0.532 : ℝ) ∧
    (cell12759 i).centre ≤ (0.1 : ℝ) ∧ (cell12759 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12759 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12759 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12759

/-! The local source numeric instances at 12759 have no network premises. -/
namespace BstLean.Part269.N12759
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12759)
open BstLean.Part268 (cell12759)

noncomputable def sourceNumerics12759 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12759 (cell12759 i)
      scalarRow12759.M scalarRow12759.H scalarRow12759.xi := by
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
    energy_allowance := scalarRow12759.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12759]
    centre_nonneg := (scalarRow12759.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12759])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12759
/-! Actual 12760 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12760 ≤ (1.035724191214 : ℝ) := by
  have hr : (112.960169971543 : ℝ) ≤ √(12760 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.960169971543 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12760 12760 (11 / 1000) ≤
    (0.008462159822 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12760) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.960169971543 : ℝ) ≤ √(12760 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12760)
  have hdiv : K / √(12760 : ℝ) ≤ K / 112.960169971543 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.960169971543 ≤ (0.008462159822 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12760.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12760 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12760 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12760 := gPlus_lower 12760
end BstLean.Part269.N12760

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12760
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035724191213 : ℝ) ≤ wn 12760 := by
  have hn : √(12760 : ℝ) ≤ 112.960169971544 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12760 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.960169971544 ≤ 2 / √(12760 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250675896 : ℝ) ≤ rhoBar 12760 BstLean.Part154.csC ∧
    rhoBar 12760 BstLean.Part154.csC ≤ 0.000250676285 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035724191213 : ℝ) / (1.295212 * 12760) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035724191214 : ℝ) / (1.29521 * 12760) := by gcongr
      _ ≤ (0.000250676285 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12760 BstLean.Part154.csC) ≤ 0.001002767979 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12760 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) ≤ 0.000191468195 ∧
    cc1 (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) ≤ 0.000121832493 ∧
    cc2 (rhoBar 12760 BstLean.Part154.csC) ≤ 0.000070724706 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12760 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12760 BstLean.Part154.csC * nuR (rhoBar 12760 BstLean.Part154.csC)) ≤ 0.000501368280 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250676285 : ℝ) * 0.001002767979 := by gcongr
      _ ≤ (0.000501368280 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12760 BstLean.Part154.csC) * nuR (rhoBar 12760 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002767979 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12760 BstLean.Part154.csC) * rhoBar 12760 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250676285 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250676285 / 2 + 0.399 * 0.001002767979 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191468195 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501368280 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121832493 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250676285 / 1.414213562 := by gcongr
      _ ≤ (0.000070724706 : ℝ) := by norm_num

end BstLean.Part269.N12760

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12760
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) ≤ 1.58317E-7 := by
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12760 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12760 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191468195 : ℝ) ^ 2 + 0.000121832493 ^ 2 + 3 * 0.000070724706 ^ 2 +
        2 * 0.797885 * 0.000191468195 * 0.000121832493 + 2 * 0.000191468195 * 0.000070724706 +
        4 * 0.797885 * 0.000121832493 * 0.000070724706 := by gcongr
    _ ≤ (1.58317E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12760 BstLean.Part154.csC Θ ≤ 0.002616490048 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12760 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12760 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035724191214 * 1.58317E-7 / (0.000250675896 : ℝ) := by gcongr
    _ ≤ 0.002616490048 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12760 BstLean.Part154.csC Θ ≤ 0.002902904240 + 0.000661146305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12760 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035724191214 : ℝ) * ((2 * Θ * 0.000250676285 +
        (6863 / 10000) * 0.000250676285 * 12760 * 0.001002767979) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002902904240 + 0.000661146305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12760 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12760 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12760 0.011 Θ ∧ gammaRatio 12760 0.011 Θ ≤ 0.000086176025 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12760 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035724191214 : ℝ) * 0.525 / ((1 - 0.011) * 12760) := by gcongr
      _ ≤ (0.000086176025 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12760 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12760 0.011 Θ) :=
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
    badAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12760 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12760 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12760 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12760 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12760 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12760 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12760 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12760 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12760 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12760 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035724191214 : ℝ) * 12760 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003463065710 + 0.003277636353 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12760

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12760
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12760 BstLean.Part154.csC) (piBar (rhoBar 12760 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12760 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12760 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12760 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12760 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12760 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12760 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12760 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12760 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12760 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052359435219 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12760) ≤ 0.010572200639 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12760 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035724191214)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010572200639 + 2 * 0.737676 / 12760) := by gcongr
    _ ≤ (0.052359435219 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12760 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12760

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12760
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506268910 : ℝ) ≤ plow 12760 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12760) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690424796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373657276) : eMP 12760 0.011 xi bn ≤ 0.001182672055 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12760 : ℝ) * (1 - 0.011))) ≤ 0.000584777525 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373657276 / (12760 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584777525 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584777525 : ℝ) + 3.141593 * 0.052690424796 / (12760 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182672055 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690424796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373657276) : PiBarMP 12760 12 0.011 xi bn ≤ 0.160867554844 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12760 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037062882727 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.337171052149 : ℝ) ≤ √((12760 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.960169971543 : ℝ) ≤ √(12760 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12760) ≤ 0.123339122687 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037062882727 + 0.052690424796 * 1.772454 / (2 * (112.337171052149 : ℝ))) * (1 + 0.001182672055) +
        8 / (12760 * 112.960169971543) + 0.123339122687 := by gcongr
    _ ≤ (0.160867554844 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690424796)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373657276) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281903384815) :
    parallelOracle 12760 0.011 xi bn cd ≤ 0.161853252202 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12760 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12760 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506268910 : ℝ) ≤ plow 12760 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.960169971543 : ℝ) ≤ √(12760 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281903384815 : ℝ) / (2 * 0.560506268910 * 112.960169971543)) * 0.160867554844 +
        0.281903384815 ^ 2 / (2 * 0.560506268910 * 112.960169971543) := by gcongr
    _ ≤ (0.161853252202 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690424796) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373657276)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281903384815) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12760 12760 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506268910 : ℝ) ≤ plow 12760 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.960169971543 : ℝ) ≤ √(12760 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12760 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12760 Θ 1.22 ≤ 0.011739540587 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.960169971543 := by gcongr <;> linarith
      _ ≤ (0.011739540587 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12760 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12760 12760 0.011 ≤ 0.008462159822 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12760 12760 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12760 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12760 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12760 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12760 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161853252202 + 0.011739540587 + (0.008462159822 : ℝ) *
        (1 + 2 * (0.281903384815 + 0.011739540587) / (0.560506268910 * 112.960169971543))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12760]

end BstLean.Part269.N12760

/-! The original eight local profiles supply actual 12760 moment certificates. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12760 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052690424796 ∧
    0 ≤ bN 12760 BstLean.Part154.csC (groupTheta g) ∧ bN 12760 BstLean.Part154.csC (groupTheta g) ≤ 0.001373657276 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12760 12760 0.011
      (momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12760 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12760 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12760 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229543949596 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12760 0.011
      (momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12760 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12760
/-! The actual computed-centre upper energy formula at 12760. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12760

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12760)
open BstLean.Part268 (cell12760)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085317190862
  | 2 => 0.086256803459
  | 3 => 0.087194105061
  | 4 => 0.088130409435
  | 5 => 0.089067309012
  | 6 => 0.090006716715
  | 7 => 0.090950911794
  | 8 => 0.091902589740
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12760 12760 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12760 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12760

/-! Actual upper energy certificates on all 43 source endpoints at 12760. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12760)
open BstLean.Part268 (cell12760)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12760 (gMinus 12760) (1 - (cell12760 i).lower) ≤ 1 ∧
    energyUpper 12760 (gMinus 12760) (BstLean.Part211.gPlus 12760)
      (finiteEnergy 12760 12760 0.011) (1 - (cell12760 i).lower) ≤
      (cell12760 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨10,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨11,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨12,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨13,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨14,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨15,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨16,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨17,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨18,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨19,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨20,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨21,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨22,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨23,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨24,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨25,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨26,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨27,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨28,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨29,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨30,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨31,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨32,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨33,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨34,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨35,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨36,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨37,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨38,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨39,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨40,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨41,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨42,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨43,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨44,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨45,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨46,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨47,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨48,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨49,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨50,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨51,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12760) (by norm_num)
        (q := 1 - (cell12760 ⟨52,by decide⟩).lower)
        (by norm_num [cell12760]) (by norm_num [cell12760])
      exact ⟨E.1,E.2.trans (by norm_num [cell12760])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12760

/-! Source-cell containment and simple scalar guards at 12760. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12760)
open BstLean.Part268 (cell12760)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12760 ⟨10,by decide⟩).lower ∧ (cell12760 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12760 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12760 ⟨11,by decide⟩).lower ∧ (cell12760 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12760 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12760 ⟨12,by decide⟩).lower ∧ (cell12760 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12760 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12760 ⟨13,by decide⟩).lower ∧ (cell12760 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12760 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12760 ⟨14,by decide⟩).lower ∧ (cell12760 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12760 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12760 ⟨15,by decide⟩).lower ∧ (cell12760 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12760 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12760 ⟨16,by decide⟩).lower ∧ (cell12760 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12760 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12760 ⟨17,by decide⟩).lower ∧ (cell12760 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12760 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12760 ⟨18,by decide⟩).lower ∧ (cell12760 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12760 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12760 ⟨19,by decide⟩).lower ∧ (cell12760 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12760 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12760 ⟨20,by decide⟩).lower ∧ (cell12760 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12760 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12760 ⟨21,by decide⟩).lower ∧ (cell12760 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12760 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12760 ⟨22,by decide⟩).lower ∧ (cell12760 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12760 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12760 ⟨23,by decide⟩).lower ∧ (cell12760 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12760 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12760 ⟨24,by decide⟩).lower ∧ (cell12760 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12760 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12760 ⟨25,by decide⟩).lower ∧ (cell12760 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12760 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12760 ⟨26,by decide⟩).lower ∧ (cell12760 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12760 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12760 ⟨27,by decide⟩).lower ∧ (cell12760 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12760 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12760 ⟨28,by decide⟩).lower ∧ (cell12760 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12760 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12760 ⟨29,by decide⟩).lower ∧ (cell12760 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12760 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12760 ⟨30,by decide⟩).lower ∧ (cell12760 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12760 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12760 ⟨31,by decide⟩).lower ∧ (cell12760 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12760 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12760 ⟨32,by decide⟩).lower ∧ (cell12760 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12760 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12760 ⟨33,by decide⟩).lower ∧ (cell12760 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12760 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12760 ⟨34,by decide⟩).lower ∧ (cell12760 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12760 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12760 ⟨35,by decide⟩).lower ∧ (cell12760 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12760 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12760 ⟨36,by decide⟩).lower ∧ (cell12760 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12760 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12760 ⟨37,by decide⟩).lower ∧ (cell12760 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12760 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12760 ⟨38,by decide⟩).lower ∧ (cell12760 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12760 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12760 ⟨39,by decide⟩).lower ∧ (cell12760 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12760 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12760 ⟨40,by decide⟩).lower ∧ (cell12760 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12760 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12760 ⟨41,by decide⟩).lower ∧ (cell12760 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12760 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12760 ⟨42,by decide⟩).lower ∧ (cell12760 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12760 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12760 ⟨43,by decide⟩).lower ∧ (cell12760 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12760 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12760 ⟨44,by decide⟩).lower ∧ (cell12760 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12760 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12760 ⟨45,by decide⟩).lower ∧ (cell12760 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12760 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12760 ⟨46,by decide⟩).lower ∧ (cell12760 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12760 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12760 ⟨47,by decide⟩).lower ∧ (cell12760 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12760 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12760 ⟨48,by decide⟩).lower ∧ (cell12760 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12760 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12760 ⟨49,by decide⟩).lower ∧ (cell12760 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12760 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12760 ⟨50,by decide⟩).lower ∧ (cell12760 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12760 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12760 ⟨51,by decide⟩).lower ∧ (cell12760 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12760 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12760 ⟨52,by decide⟩).lower ∧ (cell12760 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12760 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12760 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12760 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12760,cell12760,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12760 i).lower ∧
    (cell12760 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12760 i).upper ≤ (0.532 : ℝ) ∧
    (cell12760 i).centre ≤ (0.1 : ℝ) ∧ (cell12760 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12760 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12760 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12760

/-! The local source numeric instances at 12760 have no network premises. -/
namespace BstLean.Part269.N12760
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12760)
open BstLean.Part268 (cell12760)

noncomputable def sourceNumerics12760 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12760 (cell12760 i)
      scalarRow12760.M scalarRow12760.H scalarRow12760.xi := by
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
    energy_allowance := scalarRow12760.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12760]
    centre_nonneg := (scalarRow12760.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12760])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12760
/-! Actual 12761 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12761 ≤ (1.035722779163 : ℝ) := by
  have hr : (112.964596223772 : ℝ) ≤ √(12761 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.964596223772 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12761 12761 (11 / 1000) ≤
    (0.008461828250 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12761) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.964596223772 : ℝ) ≤ √(12761 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12761)
  have hdiv : K / √(12761 : ℝ) ≤ K / 112.964596223772 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.964596223772 ≤ (0.008461828250 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12761.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12761 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12761 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12761 := gPlus_lower 12761
end BstLean.Part269.N12761

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12761
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035722779162 : ℝ) ≤ wn 12761 := by
  have hn : √(12761 : ℝ) ≤ 112.964596223773 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12761 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.964596223773 ≤ 2 / √(12761 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250655911 : ℝ) ≤ rhoBar 12761 BstLean.Part154.csC ∧
    rhoBar 12761 BstLean.Part154.csC ≤ 0.000250656299 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035722779162 : ℝ) / (1.295212 * 12761) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035722779163 : ℝ) / (1.29521 * 12761) := by gcongr
      _ ≤ (0.000250656299 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12761 BstLean.Part154.csC) ≤ 0.001002688025 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12761 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) ≤ 0.000191452929 ∧
    cc1 (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) ≤ 0.000121822779 ∧
    cc2 (rhoBar 12761 BstLean.Part154.csC) ≤ 0.000070719067 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12761 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12761 BstLean.Part154.csC * nuR (rhoBar 12761 BstLean.Part154.csC)) ≤ 0.000501328306 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250656299 : ℝ) * 0.001002688025 := by gcongr
      _ ≤ (0.000501328306 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12761 BstLean.Part154.csC) * nuR (rhoBar 12761 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002688025 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12761 BstLean.Part154.csC) * rhoBar 12761 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250656299 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250656299 / 2 + 0.399 * 0.001002688025 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191452929 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501328306 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121822779 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250656299 / 1.414213562 := by gcongr
      _ ≤ (0.000070719067 : ℝ) := by norm_num

end BstLean.Part269.N12761

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12761
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) ≤ 1.58292E-7 := by
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12761 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12761 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191452929 : ℝ) ^ 2 + 0.000121822779 ^ 2 + 3 * 0.000070719067 ^ 2 +
        2 * 0.797885 * 0.000191452929 * 0.000121822779 + 2 * 0.000191452929 * 0.000070719067 +
        4 * 0.797885 * 0.000121822779 * 0.000070719067 := by gcongr
    _ ≤ (1.58292E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12761 BstLean.Part154.csC Θ ≤ 0.002616281891 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12761 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12761 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035722779163 * 1.58292E-7 / (0.000250655911 : ℝ) := by gcongr
    _ ≤ 0.002616281891 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12761 BstLean.Part154.csC Θ ≤ 0.002902664863 + 0.000661092691 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12761 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035722779163 : ℝ) * ((2 * Θ * 0.000250656299 +
        (6863 / 10000) * 0.000250656299 * 12761 * 0.001002688025) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002902664863 + 0.000661092691 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12761 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12761 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12761 0.011 Θ ∧ gammaRatio 12761 0.011 Θ ≤ 0.000086169154 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12761 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035722779163 : ℝ) * 0.525 / ((1 - 0.011) * 12761) := by gcongr
      _ ≤ (0.000086169154 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12761 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12761 0.011 Θ) :=
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
    badAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12761 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12761 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12761 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12761 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12761 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12761 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12761 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12761 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12761 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12761 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035722779163 : ℝ) * 12761 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003462826333 + 0.003277374582 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12761

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12761
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12761 BstLean.Part154.csC) (piBar (rhoBar 12761 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12761 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12761 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12761 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12761 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12761 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12761 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12761 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12761 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12761 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052357361443 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12761) ≤ 0.010571786392 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12761 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035722779163)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010571786392 + 2 * 0.737676 / 12761) := by gcongr
    _ ≤ (0.052357361443 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12761 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12761

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12761
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506313705 : ℝ) ≤ plow 12761 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12761) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690047989)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373547993) : eMP 12761 0.011 xi bn ≤ 0.001182578585 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12761 : ℝ) * (1 - 0.011))) ≤ 0.000584731351 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373547993 / (12761 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584731351 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584731351 : ℝ) + 3.141593 * 0.052690047989 / (12761 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182578585 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690047989)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373547993) : PiBarMP 12761 12 0.011 xi bn ≤ 0.160861222588 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12761 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037061408406 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.341572892674 : ℝ) ≤ √((12761 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.964596223772 : ℝ) ≤ √(12761 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12761) ≤ 0.123334289933 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037061408406 + 0.052690047989 * 1.772454 / (2 * (112.341572892674 : ℝ))) * (1 + 0.001182578585) +
        8 / (12761 * 112.964596223772) + 0.123334289933 := by gcongr
    _ ≤ (0.160861222588 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690047989)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373547993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281900490265) :
    parallelOracle 12761 0.011 xi bn cd ≤ 0.161846850585 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12761 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12761 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506313705 : ℝ) ≤ plow 12761 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.964596223772 : ℝ) ≤ √(12761 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281900490265 : ℝ) / (2 * 0.560506313705 * 112.964596223772)) * 0.160861222588 +
        0.281900490265 ^ 2 / (2 * 0.560506313705 * 112.964596223772) := by gcongr
    _ ≤ (0.161846850585 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052690047989) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373547993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281900490265) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12761 12761 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506313705 : ℝ) ≤ plow 12761 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.964596223772 : ℝ) ≤ √(12761 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12761 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12761 Θ 1.22 ≤ 0.011739080600 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.964596223772 := by gcongr <;> linarith
      _ ≤ (0.011739080600 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12761 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12761 12761 0.011 ≤ 0.008461828250 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12761 12761 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12761 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12761 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12761 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12761 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161846850585 + 0.011739080600 + (0.008461828250 : ℝ) *
        (1 + 2 * (0.281900490265 + 0.011739080600) / (0.560506313705 * 112.964596223772))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12761]

end BstLean.Part269.N12761

/-! The original eight local profiles supply actual 12761 moment certificates. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12761 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052690047989 ∧
    0 ≤ bN 12761 BstLean.Part154.csC (groupTheta g) ∧ bN 12761 BstLean.Part154.csC (groupTheta g) ≤ 0.001373547993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12761 12761 0.011
      (momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12761 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12761 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12761 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229543128822 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12761 0.011
      (momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12761 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12761
/-! The actual computed-centre upper energy formula at 12761. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12761

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12761)
open BstLean.Part268 (cell12761)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085314338188
  | 2 => 0.086253899795
  | 3 => 0.087191143200
  | 4 => 0.088127380493
  | 5 => 0.089064202130
  | 6 => 0.090003518723
  | 7 => 0.090947606835
  | 8 => 0.091899158849
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12761 12761 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12761 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12761

/-! Actual upper energy certificates on all 43 source endpoints at 12761. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12761)
open BstLean.Part268 (cell12761)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12761 (gMinus 12761) (1 - (cell12761 i).lower) ≤ 1 ∧
    energyUpper 12761 (gMinus 12761) (BstLean.Part211.gPlus 12761)
      (finiteEnergy 12761 12761 0.011) (1 - (cell12761 i).lower) ≤
      (cell12761 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨10,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨11,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨12,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨13,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨14,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨15,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨16,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨17,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨18,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨19,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨20,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨21,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨22,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨23,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨24,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨25,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨26,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨27,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨28,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨29,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨30,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨31,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨32,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨33,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨34,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨35,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨36,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨37,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨38,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨39,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨40,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨41,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨42,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨43,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨44,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨45,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨46,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨47,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨48,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨49,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨50,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨51,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12761) (by norm_num)
        (q := 1 - (cell12761 ⟨52,by decide⟩).lower)
        (by norm_num [cell12761]) (by norm_num [cell12761])
      exact ⟨E.1,E.2.trans (by norm_num [cell12761])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12761

/-! Source-cell containment and simple scalar guards at 12761. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12761)
open BstLean.Part268 (cell12761)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12761 ⟨10,by decide⟩).lower ∧ (cell12761 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12761 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12761 ⟨11,by decide⟩).lower ∧ (cell12761 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12761 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12761 ⟨12,by decide⟩).lower ∧ (cell12761 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12761 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12761 ⟨13,by decide⟩).lower ∧ (cell12761 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12761 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12761 ⟨14,by decide⟩).lower ∧ (cell12761 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12761 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12761 ⟨15,by decide⟩).lower ∧ (cell12761 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12761 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12761 ⟨16,by decide⟩).lower ∧ (cell12761 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12761 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12761 ⟨17,by decide⟩).lower ∧ (cell12761 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12761 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12761 ⟨18,by decide⟩).lower ∧ (cell12761 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12761 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12761 ⟨19,by decide⟩).lower ∧ (cell12761 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12761 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12761 ⟨20,by decide⟩).lower ∧ (cell12761 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12761 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12761 ⟨21,by decide⟩).lower ∧ (cell12761 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12761 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12761 ⟨22,by decide⟩).lower ∧ (cell12761 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12761 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12761 ⟨23,by decide⟩).lower ∧ (cell12761 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12761 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12761 ⟨24,by decide⟩).lower ∧ (cell12761 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12761 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12761 ⟨25,by decide⟩).lower ∧ (cell12761 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12761 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12761 ⟨26,by decide⟩).lower ∧ (cell12761 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12761 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12761 ⟨27,by decide⟩).lower ∧ (cell12761 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12761 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12761 ⟨28,by decide⟩).lower ∧ (cell12761 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12761 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12761 ⟨29,by decide⟩).lower ∧ (cell12761 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12761 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12761 ⟨30,by decide⟩).lower ∧ (cell12761 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12761 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12761 ⟨31,by decide⟩).lower ∧ (cell12761 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12761 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12761 ⟨32,by decide⟩).lower ∧ (cell12761 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12761 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12761 ⟨33,by decide⟩).lower ∧ (cell12761 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12761 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12761 ⟨34,by decide⟩).lower ∧ (cell12761 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12761 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12761 ⟨35,by decide⟩).lower ∧ (cell12761 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12761 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12761 ⟨36,by decide⟩).lower ∧ (cell12761 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12761 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12761 ⟨37,by decide⟩).lower ∧ (cell12761 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12761 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12761 ⟨38,by decide⟩).lower ∧ (cell12761 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12761 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12761 ⟨39,by decide⟩).lower ∧ (cell12761 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12761 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12761 ⟨40,by decide⟩).lower ∧ (cell12761 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12761 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12761 ⟨41,by decide⟩).lower ∧ (cell12761 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12761 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12761 ⟨42,by decide⟩).lower ∧ (cell12761 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12761 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12761 ⟨43,by decide⟩).lower ∧ (cell12761 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12761 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12761 ⟨44,by decide⟩).lower ∧ (cell12761 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12761 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12761 ⟨45,by decide⟩).lower ∧ (cell12761 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12761 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12761 ⟨46,by decide⟩).lower ∧ (cell12761 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12761 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12761 ⟨47,by decide⟩).lower ∧ (cell12761 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12761 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12761 ⟨48,by decide⟩).lower ∧ (cell12761 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12761 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12761 ⟨49,by decide⟩).lower ∧ (cell12761 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12761 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12761 ⟨50,by decide⟩).lower ∧ (cell12761 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12761 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12761 ⟨51,by decide⟩).lower ∧ (cell12761 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12761 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12761 ⟨52,by decide⟩).lower ∧ (cell12761 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12761 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12761 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12761 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12761,cell12761,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12761 i).lower ∧
    (cell12761 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12761 i).upper ≤ (0.532 : ℝ) ∧
    (cell12761 i).centre ≤ (0.1 : ℝ) ∧ (cell12761 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12761 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12761 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12761

/-! The local source numeric instances at 12761 have no network premises. -/
namespace BstLean.Part269.N12761
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12761)
open BstLean.Part268 (cell12761)

noncomputable def sourceNumerics12761 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12761 (cell12761 i)
      scalarRow12761.M scalarRow12761.H scalarRow12761.xi := by
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
    energy_allowance := scalarRow12761.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12761]
    centre_nonneg := (scalarRow12761.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12761])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12761
/-! Actual 12762 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12762 ≤ (1.035721367279 : ℝ) := by
  have hr : (112.969022302576 : ℝ) ≤ √(12762 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.969022302576 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12762 12762 (11 / 1000) ≤
    (0.008461496716 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12762) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.969022302576 : ℝ) ≤ √(12762 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12762)
  have hdiv : K / √(12762 : ℝ) ≤ K / 112.969022302576 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.969022302576 ≤ (0.008461496716 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12762.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12762 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12762 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12762 := gPlus_lower 12762
end BstLean.Part269.N12762

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12762
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035721367278 : ℝ) ≤ wn 12762 := by
  have hn : √(12762 : ℝ) ≤ 112.969022302577 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12762 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.969022302577 ≤ 2 / √(12762 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000250635928 : ℝ) ≤ rhoBar 12762 BstLean.Part154.csC ∧
    rhoBar 12762 BstLean.Part154.csC ≤ 0.000250636316 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035721367278 : ℝ) / (1.295212 * 12762) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035721367279 : ℝ) / (1.29521 * 12762) := by gcongr
      _ ≤ (0.000250636316 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12762 BstLean.Part154.csC) ≤ 0.001002608083 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12762 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) ≤ 0.000191437665 ∧
    cc1 (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) ≤ 0.000121813066 ∧
    cc2 (rhoBar 12762 BstLean.Part154.csC) ≤ 0.000070713429 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12762 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12762 BstLean.Part154.csC * nuR (rhoBar 12762 BstLean.Part154.csC)) ≤ 0.000501288337 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000250636316 : ℝ) * 0.001002608083 := by gcongr
      _ ≤ (0.000501288337 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12762 BstLean.Part154.csC) * nuR (rhoBar 12762 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001002608083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12762 BstLean.Part154.csC) * rhoBar 12762 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000250636316 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000250636316 / 2 + 0.399 * 0.001002608083 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000191437665 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000501288337 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121813066 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000250636316 / 1.414213562 := by gcongr
      _ ≤ (0.000070713429 : ℝ) := by norm_num

end BstLean.Part269.N12762

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12762
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) ≤ 1.58267E-7 := by
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12762 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12762 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000191437665 : ℝ) ^ 2 + 0.000121813066 ^ 2 + 3 * 0.000070713429 ^ 2 +
        2 * 0.797885 * 0.000191437665 * 0.000121813066 + 2 * 0.000191437665 * 0.000070713429 +
        4 * 0.797885 * 0.000121813066 * 0.000070713429 := by gcongr
    _ ≤ (1.58267E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12762 BstLean.Part154.csC Θ ≤ 0.002616073681 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12762 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12762 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035721367279 * 1.58267E-7 / (0.000250635928 : ℝ) := by gcongr
    _ ≤ 0.002616073681 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12762 BstLean.Part154.csC Θ ≤ 0.002902425521 + 0.000661039086 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12762 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035721367279 : ℝ) * ((2 * Θ * 0.000250636316 +
        (6863 / 10000) * 0.000250636316 * 12762 * 0.001002608083) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002902425521 + 0.000661039086 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12762 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12762 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12762 0.011 Θ ∧ gammaRatio 12762 0.011 Θ ≤ 0.000086162285 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12762 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035721367279 : ℝ) * 0.525 / ((1 - 0.011) * 12762) := by gcongr
      _ ≤ (0.000086162285 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12762 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12762 0.011 Θ) :=
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
    badAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000560161470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12762 BstLean.Part154.csC) 1.22 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 2 (rhoBar 12762 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12762 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12762 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12762 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12762 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12762 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12762 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12762 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12762 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035721367279 : ℝ) * 12762 *
        (2.0559E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000560161470 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003462586991 + 0.003277112767 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12762

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12762
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12762 BstLean.Part154.csC) (piBar (rhoBar 12762 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12762 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12762 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12762 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12762 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12762 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12762 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12762 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12762 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12762 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052355287914 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12762) ≤ 0.010571372194 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12762 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035721367279)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010571372194 + 2 * 0.737676 / 12762) := by gcongr
    _ ≤ (0.052355287914 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12762 12 ≤ 0.0015 := by
  exact BstLean.Part269.S16.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12762

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12762
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560506358493 : ℝ) ≤ plow 12762 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12762) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689671194)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373438683) : eMP 12762 0.011 xi bn ≤ 0.001182485111 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12762 : ℝ) * (1 - 0.011))) ≤ 0.000584685175 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001373438683 / (12762 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000584685175 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000584685175 : ℝ) + 3.141593 * 0.052689671194 / (12762 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001182485111 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689671194)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373438683) : PiBarMP 12762 12 0.011 xi bn ≤ 0.160854890478 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12762 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037059933662 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.345974560729 : ℝ) ≤ √((12762 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.969022302576 : ℝ) ≤ √(12762 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12762) ≤ 0.123329457747 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037059933662 + 0.052689671194 * 1.772454 / (2 * (112.345974560729 : ℝ))) * (1 + 0.001182485111) +
        8 / (12762 * 112.969022302576) + 0.123329457747 := by gcongr
    _ ≤ (0.160854890478 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689671194)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373438683) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281897595984) :
    parallelOracle 12762 0.011 xi bn cd ≤ 0.161840449123 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12762 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12762 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560506358493 : ℝ) ≤ plow 12762 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.969022302576 : ℝ) ≤ √(12762 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281897595984 : ℝ) / (2 * 0.560506358493 * 112.969022302576)) * 0.160854890478 +
        0.281897595984 ^ 2 / (2 * 0.560506358493 * 112.969022302576) := by gcongr
    _ ≤ (0.161840449123 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052689671194) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001373438683)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281897595984) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12762 12762 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560506358493 : ℝ) ≤ plow 12762 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.969022302576 : ℝ) ≤ √(12762 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12762 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12762 Θ 1.22 ≤ 0.011738620668 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.969022302576 := by gcongr <;> linarith
      _ ≤ (0.011738620668 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12762 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12762 12762 0.011 ≤ 0.008461496716 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12762 12762 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12762 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12762 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12762 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12762 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161840449123 + 0.011738620668 + (0.008461496716 : ℝ) *
        (1 + 2 * (0.281897595984 + 0.011738620668) / (0.560506358493 * 112.969022302576))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12762]

end BstLean.Part269.N12762

/-! The original eight local profiles supply actual 12762 moment certificates. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12762 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052689671194 ∧
    0 ≤ bN 12762 BstLean.Part154.csC (groupTheta g) ∧ bN 12762 BstLean.Part154.csC (groupTheta g) ≤ 0.001373438683 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12762 12762 0.011
      (momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12762 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12762 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12762 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229542308070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12762 0.011
      (momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12762 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12762
/-! The actual computed-centre upper energy formula at 12762. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12762

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12762)
open BstLean.Part268 (cell12762)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085311486534
  | 2 => 0.086250997192
  | 3 => 0.087188182451
  | 4 => 0.088124352725
  | 5 => 0.089061096498
  | 6 => 0.090000322074
  | 7 => 0.090944303331
  | 8 => 0.091895729549
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12762 12762 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12762 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12762

/-! Actual upper energy certificates on all 43 source endpoints at 12762. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12762)
open BstLean.Part268 (cell12762)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12762 (gMinus 12762) (1 - (cell12762 i).lower) ≤ 1 ∧
    energyUpper 12762 (gMinus 12762) (BstLean.Part211.gPlus 12762)
      (finiteEnergy 12762 12762 0.011) (1 - (cell12762 i).lower) ≤
      (cell12762 i).energy := by
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
      have E := BstLean.Part269.S16.uniformEnergy10 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨10,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy11 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨11,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy12 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨12,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy13 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨13,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy14 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨14,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy15 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨15,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy16 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨16,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy17 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨17,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy18 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨18,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy19 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨19,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy20 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨20,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy21 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨21,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy22 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨22,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy23 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨23,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy24 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨24,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy25 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨25,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy26 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨26,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy27 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨27,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy28 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨28,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy29 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨29,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy30 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨30,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy31 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨31,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy32 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨32,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy33 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨33,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy34 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨34,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy35 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨35,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy36 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨36,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy37 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨37,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy38 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨38,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy39 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨39,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy40 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨40,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy41 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨41,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy42 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨42,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy43 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨43,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy44 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨44,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy45 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨45,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy46 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨46,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy47 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨47,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy48 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨48,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy49 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨49,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy50 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨50,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy51 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨51,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S16.uniformEnergy52 (n := 12762) (by norm_num)
        (q := 1 - (cell12762 ⟨52,by decide⟩).lower)
        (by norm_num [cell12762]) (by norm_num [cell12762])
      exact ⟨E.1,E.2.trans (by norm_num [cell12762])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12762

/-! Source-cell containment and simple scalar guards at 12762. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12762)
open BstLean.Part268 (cell12762)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12762 ⟨10,by decide⟩).lower ∧ (cell12762 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12762 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12762 ⟨11,by decide⟩).lower ∧ (cell12762 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12762 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12762 ⟨12,by decide⟩).lower ∧ (cell12762 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12762 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12762 ⟨13,by decide⟩).lower ∧ (cell12762 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12762 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12762 ⟨14,by decide⟩).lower ∧ (cell12762 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12762 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12762 ⟨15,by decide⟩).lower ∧ (cell12762 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12762 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12762 ⟨16,by decide⟩).lower ∧ (cell12762 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12762 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12762 ⟨17,by decide⟩).lower ∧ (cell12762 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12762 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12762 ⟨18,by decide⟩).lower ∧ (cell12762 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12762 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12762 ⟨19,by decide⟩).lower ∧ (cell12762 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12762 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12762 ⟨20,by decide⟩).lower ∧ (cell12762 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12762 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12762 ⟨21,by decide⟩).lower ∧ (cell12762 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12762 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12762 ⟨22,by decide⟩).lower ∧ (cell12762 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12762 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12762 ⟨23,by decide⟩).lower ∧ (cell12762 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12762 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12762 ⟨24,by decide⟩).lower ∧ (cell12762 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12762 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12762 ⟨25,by decide⟩).lower ∧ (cell12762 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12762 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12762 ⟨26,by decide⟩).lower ∧ (cell12762 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12762 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12762 ⟨27,by decide⟩).lower ∧ (cell12762 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12762 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12762 ⟨28,by decide⟩).lower ∧ (cell12762 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12762 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12762 ⟨29,by decide⟩).lower ∧ (cell12762 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12762 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12762 ⟨30,by decide⟩).lower ∧ (cell12762 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12762 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12762 ⟨31,by decide⟩).lower ∧ (cell12762 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12762 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12762 ⟨32,by decide⟩).lower ∧ (cell12762 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12762 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12762 ⟨33,by decide⟩).lower ∧ (cell12762 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12762 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12762 ⟨34,by decide⟩).lower ∧ (cell12762 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12762 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12762 ⟨35,by decide⟩).lower ∧ (cell12762 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12762 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12762 ⟨36,by decide⟩).lower ∧ (cell12762 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12762 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12762 ⟨37,by decide⟩).lower ∧ (cell12762 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12762 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12762 ⟨38,by decide⟩).lower ∧ (cell12762 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12762 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12762 ⟨39,by decide⟩).lower ∧ (cell12762 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12762 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12762 ⟨40,by decide⟩).lower ∧ (cell12762 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12762 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12762 ⟨41,by decide⟩).lower ∧ (cell12762 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12762 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12762 ⟨42,by decide⟩).lower ∧ (cell12762 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12762 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12762 ⟨43,by decide⟩).lower ∧ (cell12762 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12762 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12762 ⟨44,by decide⟩).lower ∧ (cell12762 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12762 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12762 ⟨45,by decide⟩).lower ∧ (cell12762 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12762 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12762 ⟨46,by decide⟩).lower ∧ (cell12762 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12762 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12762 ⟨47,by decide⟩).lower ∧ (cell12762 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12762 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12762 ⟨48,by decide⟩).lower ∧ (cell12762 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12762 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12762 ⟨49,by decide⟩).lower ∧ (cell12762 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12762 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12762 ⟨50,by decide⟩).lower ∧ (cell12762 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12762 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12762 ⟨51,by decide⟩).lower ∧ (cell12762 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12762 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12762 ⟨52,by decide⟩).lower ∧ (cell12762 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12762 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12762 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12762 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12762,cell12762,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12762 i).lower ∧
    (cell12762 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12762 i).upper ≤ (0.532 : ℝ) ∧
    (cell12762 i).centre ≤ (0.1 : ℝ) ∧ (cell12762 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12762 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12762 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12762

/-! The local source numeric instances at 12762 have no network premises. -/
namespace BstLean.Part269.N12762
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12762)
open BstLean.Part268 (cell12762)

noncomputable def sourceNumerics12762 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12762 (cell12762 i)
      scalarRow12762.M scalarRow12762.H scalarRow12762.xi := by
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
    energy_allowance := scalarRow12762.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12762]
    centre_nonneg := (scalarRow12762.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D16.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12762])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12762